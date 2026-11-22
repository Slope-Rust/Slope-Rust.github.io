// Videos in the browser version (SAVE VIDEO of a saved run, and "Record every run I play"): the
// game hands over its pictures and its music, the browser's own encoders (WebCodecs) make them
// into H.264 (or VP9) and AAC (or Opus), and this file puts those into an MP4 file, which the
// browser saves as a download. The desktop game does the same with Windows' encoder (src/video.rs).
//
// The game asks:  slope_video_start  a video of this size, rate and bit rate (and its file name)
//                 slope_video_room   whether it can take another picture now (the encoder is not behind)
//                 slope_video_picture / slope_video_canvas   a picture (from the game's memory, or the
//                                    page's canvas as it is), and slope_video_sound  more of the sound
//                 slope_video_close  that was all: the file is made and saved
//                 slope_video_state  0 still at it, 1 saved, 2 failed (slope_video_reason says why),
//                                    3 given up (slope_video_cancel)
(function () {
  "use strict";
  var canVideo = typeof VideoEncoder === "function" && typeof VideoFrame === "function";
  var canSound = typeof AudioEncoder === "function" && typeof AudioData === "function";
  var jobs = new Map(), next = 1, lastReason = "";

  // ---- bytes and boxes of an MP4 file ----
  function W() { this.a = new Uint8Array(1024); this.n = 0; }
  W.prototype.room = function (k) {
    if (this.n + k <= this.a.length) return;
    var b = new Uint8Array(Math.max(this.a.length * 2, this.n + k));
    b.set(this.a.subarray(0, this.n));
    this.a = b;
  };
  W.prototype.u8 = function (v) { this.room(1); this.a[this.n++] = v & 255; return this; };
  W.prototype.u16 = function (v) { return this.u8(v >>> 8).u8(v); };
  W.prototype.u24 = function (v) { return this.u8(v >>> 16).u16(v & 0xffff); };
  W.prototype.u32 = function (v) { v = v >>> 0; return this.u16(v >>> 16).u16(v & 0xffff); };
  W.prototype.u64 = function (v) { var hi = Math.floor(v / 4294967296); return this.u32(hi).u32(v - hi * 4294967296); };
  W.prototype.str = function (s) { for (var i = 0; i < s.length; i++) this.u8(s.charCodeAt(i)); return this; };
  W.prototype.bytes = function (b) { this.room(b.length); this.a.set(b, this.n); this.n += b.length; return this; };
  W.prototype.zeros = function (k) { for (var i = 0; i < k; i++) this.u8(0); return this; };
  W.prototype.done = function () { return this.a.slice(0, this.n); };
  function cat(list) {
    var n = 0, at = 0;
    list.forEach(function (b) { n += b.length; });
    var out = new Uint8Array(n);
    list.forEach(function (b) { out.set(b, at); at += b.length; });
    return out;
  }
  function box(type) {
    var body = cat(Array.prototype.slice.call(arguments, 1));
    return new W().u32(8 + body.length).str(type).bytes(body).done();
  }
  function full(type, version, flags) {
    var head = new W().u8(version).u24(flags).done();
    return box.apply(null, [type, head].concat(Array.prototype.slice.call(arguments, 3)));
  }
  var MATRIX = [0x00010000, 0, 0, 0, 0x00010000, 0, 0, 0, 0x40000000];
  function matrix(w) { MATRIX.forEach(function (v) { w.u32(v); }); return w; }
  // (a descriptor of the MPEG-4 sound's description: tag, length, contents)
  function desc(tag, body) {
    var w = new W().u8(tag), n = body.length;
    w.u8(0x80 | (n >>> 21) & 127).u8(0x80 | (n >>> 14) & 127).u8(0x80 | (n >>> 7) & 127).u8(n & 127);
    return w.bytes(body).done();
  }
  // durations as runs of equal ones
  function stts(durs) {
    var runs = [];
    durs.forEach(function (d) {
      if (runs.length && runs[runs.length - 1][1] === d) runs[runs.length - 1][0]++;
      else runs.push([1, d]);
    });
    var w = new W().u32(runs.length);
    runs.forEach(function (r) { w.u32(r[0]).u32(r[1]); });
    return full("stts", 0, 0, w.done());
  }
  function sampleTable(t, entry, wide) {
    var s = t.samples, parts = [full("stsd", 0, 0, new W().u32(1).done(), entry), stts(s.map(function (x) { return x.dur; }))];
    if (t.video) {
      var keys = new W(), n = 0;
      s.forEach(function (x, i) { if (x.key) { keys.u32(i + 1); n++; } });
      if (n < s.length) parts.push(full("stss", 0, 0, new W().u32(n).done(), keys.done()));
    }
    parts.push(full("stsc", 0, 0, new W().u32(1).u32(1).u32(1).u32(1).done()));
    var sizes = new W().u32(0).u32(s.length);
    s.forEach(function (x) { sizes.u32(x.size); });
    parts.push(full("stsz", 0, 0, sizes.done()));
    var offs = new W().u32(s.length);
    s.forEach(function (x) { if (wide) offs.u64(x.at); else offs.u32(x.at); });
    parts.push(full(wide ? "co64" : "stco", 0, 0, offs.done()));
    return box.apply(null, ["stbl"].concat(parts));
  }
  function track(t, id, movieMs, wide) {
    var units = t.samples.reduce(function (a, x) { return a + x.dur; }, 0);
    var tkhd = matrix(new W().u32(0).u32(0).u32(id).u32(0).u32(movieMs).zeros(8).u16(0).u16(0).u16(t.video ? 0 : 0x0100).u16(0))
      .u32(t.video ? t.width * 65536 : 0).u32(t.video ? t.height * 65536 : 0).done();
    var mdhd = new W().u32(0).u32(0).u32(t.scale).u32(units).u16(0x55c4).u16(0).done();
    var hdlr = new W().u32(0).str(t.video ? "vide" : "soun").zeros(12).str(t.video ? "VideoHandler" : "SoundHandler").u8(0).done();
    var head = t.video ? full("vmhd", 0, 1, new W().zeros(8).done()) : full("smhd", 0, 0, new W().zeros(4).done());
    var dinf = box("dinf", full("dref", 0, 0, new W().u32(1).done(), full("url ", 0, 1)));
    var entry;
    if (t.video) {
      var v = new W().zeros(6).u16(1).zeros(16).u16(t.width).u16(t.height).u32(0x00480000).u32(0x00480000).u32(0).u16(1).zeros(32).u16(0x18).u16(0xffff).done();
      entry = t.codec === "avc1"
        ? box("avc1", v, box("avcC", t.config || new Uint8Array(0)))
        : box("vp09", v, full("vpcC", 1, 0, new W().u8(0).u8(t.level || 51).u8(0x82).u8(1).u8(1).u8(1).u16(0).done()));
    } else {
      var a = new W().zeros(6).u16(1).zeros(8).u16(t.channels).u16(16).u16(0).u16(0).u32(t.rate * 65536).done();
      if (t.codec === "mp4a") {
        var asc = t.config && t.config.length ? t.config : new Uint8Array([0x12, 0x10]);
        var dcd = desc(4, cat([new W().u8(0x40).u8(0x15).u24(0).u32(t.bitrate).u32(t.bitrate).done(), desc(5, asc)]));
        entry = box("mp4a", a, full("esds", 0, 0, desc(3, cat([new W().u16(1).u8(0).done(), dcd, desc(6, new Uint8Array([2]))]))));
      } else {
        // (Opus: the pre-skip of its OpusHead, if the encoder gave one)
        var pre = t.config && t.config.length >= 12 ? t.config[10] | (t.config[11] << 8) : 312;
        entry = box("Opus", a, box("dOps", new W().u8(0).u8(t.channels).u16(pre).u32(t.inRate).u16(0).u8(0).done()));
      }
    }
    var minf = box("minf", head, dinf, sampleTable(t, entry, wide));
    return box("trak", full("tkhd", 0, 3, tkhd), box("mdia", full("mdhd", 0, 0, mdhd), full("hdlr", 0, 0, hdlr), minf));
  }
  // the whole file: ftyp, the samples (as they came), and the index of them (moov)
  function mp4(job) {
    var ftyp = box("ftyp", new W().str("isom").u32(0x200).str("isomiso2").str(job.video.codec === "avc1" ? "avc1" : "iso6").str("mp41").done());
    var mdatSize = 16 + job.bytes;
    var base = ftyp.length + 16;
    var wide = base + job.bytes > 4294000000;
    var tracks = [job.video].concat(job.audio && job.audio.samples.length ? [job.audio] : []);
    // (a picture lasts until the next one: one left out while the encoder was behind leaves the
    // one before it on the screen a little longer)
    var v = job.video.samples;
    for (var i = 0; i + 1 < v.length; i++) v[i].dur = Math.max(1, Math.round((v[i + 1].ts - v[i].ts) * job.video.scale / 1e6));
    tracks.forEach(function (t) { t.samples.forEach(function (x) { x.at = base + x.rel; }); });
    var ms = Math.round(tracks.reduce(function (m, t) {
      return Math.max(m, t.samples.reduce(function (a, x) { return a + x.dur; }, 0) * 1000 / t.scale);
    }, 0));
    var mvhd = matrix(new W().u32(0).u32(0).u32(1000).u32(ms).u32(0x00010000).u16(0x0100).zeros(10)).zeros(24).u32(tracks.length + 1).done();
    var moov = box.apply(null, ["moov", full("mvhd", 0, 0, mvhd)].concat(tracks.map(function (t, i) { return track(t, i + 1, ms, wide); })));
    var mdat = new W().u32(1).str("mdat").u64(mdatSize).done();
    return new Blob([ftyp, mdat].concat(job.data, [moov]), { type: "video/mp4" });
  }

  // ---- the encoders ----
  // (H.264's level from how many 16 x 16 blocks a second there are)
  function avcLevel(w, h, fps) {
    var fs = Math.ceil(w / 16) * Math.ceil(h / 16), mbps = fs * fps;
    if (fs <= 8704 && mbps <= 522240) return "2A";
    if (fs <= 36864 && mbps <= 983040) return "33";
    if (fs <= 36864 && mbps <= 2073600) return "34";
    return "3E";
  }
  async function pickVideo(job) {
    var s = job.spec, lv = avcLevel(s.w, s.h, s.fps);
    var codecs = ["avc1.6400" + lv, "avc1.4D00" + lv, "avc1.4200" + lv, "vp09.00.51.08", "vp09.00.61.08"];
    var hw = s.hardware ? ["prefer-hardware", "no-preference"] : ["no-preference"];
    for (var i = 0; i < codecs.length; i++) {
      for (var j = 0; j < hw.length; j++) {
        var c = { codec: codecs[i], width: s.w, height: s.h, framerate: s.fps, bitrate: s.bitrate, bitrateMode: "variable", hardwareAcceleration: hw[j], latencyMode: "quality" };
        if (codecs[i].indexOf("avc1") === 0) c.avc = { format: "avc" };
        try {
          var r = await VideoEncoder.isConfigSupported(c);
          if (r.supported) return c;
        } catch (e) {}
      }
    }
    return null;
  }
  async function pickSound() {
    if (!canSound) return null;
    var tries = [{ codec: "mp4a.40.2", sampleRate: 44100 }, { codec: "opus", sampleRate: 44100 }, { codec: "opus", sampleRate: 48000 }];
    for (var i = 0; i < tries.length; i++) {
      var c = { codec: tries[i].codec, sampleRate: tries[i].sampleRate, numberOfChannels: 2, bitrate: 192000 };
      try {
        var r = await AudioEncoder.isConfigSupported(c);
        if (r.supported) return c;
      } catch (e) {}
    }
    return null;
  }
  // (an encoder's description, as whichever kind of buffer it came)
  function bytesOf(d) {
    return d instanceof ArrayBuffer ? new Uint8Array(d.slice(0)) : new Uint8Array(d.buffer.slice(d.byteOffset, d.byteOffset + d.byteLength));
  }
  function fail(job, why) {
    if (job.state >= 3) return;
    job.state = 4;
    job.reason = why;
    try { if (job.venc && job.venc.state !== "closed") job.venc.close(); } catch (e) {}
    try { if (job.aenc && job.aenc.state !== "closed") job.aenc.close(); } catch (e) {}
    job.data = [];
  }
  function keep(job, t, chunk, dur) {
    var b = new Uint8Array(chunk.byteLength);
    chunk.copyTo(b);
    t.samples.push({ size: b.length, rel: job.bytes, key: chunk.type === "key", dur: dur, ts: chunk.timestamp });
    job.data.push(b);
    job.bytes += b.length;
  }
  function begin(job) {
    var s = job.spec;
    Promise.all([pickVideo(job), s.sound ? pickSound() : Promise.resolve(null)]).then(function (got) {
      if (job.state !== 0) return;
      var vc = got[0], ac = got[1];
      if (!vc) return fail(job, "this browser has no video encoder that takes " + s.w + " x " + s.h + " at " + s.fps + " pictures a second (try a smaller size or a lower frame rate)");
      var avc = vc.codec.indexOf("avc1") === 0;
      job.video = { video: true, codec: avc ? "avc1" : "vp09", width: s.w, height: s.h, scale: s.fps * 1000, samples: [], config: null, level: vc.codec.indexOf(".61.") > 0 ? 61 : 51 };
      job.venc = new VideoEncoder({
        output: function (chunk, meta) {
          if (job.state >= 3) return;
          if (meta && meta.decoderConfig && meta.decoderConfig.description && !job.video.config) {
            job.video.config = bytesOf(meta.decoderConfig.description);
          }
          keep(job, job.video, chunk, 1000);
          job.written++;
        },
        error: function (e) { fail(job, "the video encoder stopped: " + (e && e.message || e)); }
      });
      job.venc.configure(vc);
      job.codecs = avc ? "H.264" : "VP9";
      if (ac) {
        var aac = ac.codec === "mp4a.40.2";
        var outRate = aac ? 44100 : 48000;
        job.audio = { video: false, codec: aac ? "mp4a" : "Opus", channels: 2, rate: outRate, inRate: ac.sampleRate, scale: outRate, bitrate: 192000, samples: [], config: null };
        job.inRate = ac.sampleRate;
        job.aenc = new AudioEncoder({
          output: function (chunk, meta) {
            if (job.state >= 3) return;
            if (meta && meta.decoderConfig && meta.decoderConfig.description && !job.audio.config) {
              job.audio.config = bytesOf(meta.decoderConfig.description);
            }
            var dur = chunk.duration ? Math.round(chunk.duration * outRate / 1e6) : (aac ? 1024 : 960);
            keep(job, job.audio, chunk, dur);
          },
          error: function (e) { job.audio = null; job.aenc = null; job.note = "no sound: the sound encoder stopped"; }
        });
        job.aenc.configure(ac);
        job.codecs += aac ? ", AAC" : ", Opus";
      } else if (s.sound) {
        job.note = "no sound: this browser has no sound encoder for pages";
      }
      job.state = 1;
      // (what came while the encoders were being picked)
      var early = job.early;
      job.early = [];
      early.forEach(function (f) { f(); });
      if (job.closing) finish(job);
    }, function (e) { fail(job, String(e)); });
  }
  function encodeFrame(job, frame, index) {
    var key = job.lastKey < 0 || index - job.lastKey >= job.spec.fps * 2;
    if (key) job.lastKey = index;
    try { job.venc.encode(frame, { keyFrame: key }); } catch (e) { fail(job, "a picture could not be encoded: " + e.message); }
    frame.close();
  }
  function finish(job) {
    if (job.state !== 1) { job.closing = true; return; }
    job.state = 2;
    var waits = [job.venc.flush()];
    if (job.aenc) waits.push(job.aenc.flush().catch(function () { job.audio = null; }));
    Promise.all(waits).then(function () {
      if (job.state !== 2) return;
      try { job.venc.close(); } catch (e) {}
      try { if (job.aenc) job.aenc.close(); } catch (e) {}
      if (job.written > 0) {
        var blob = mp4(job);
        job.size = blob.size;
        if (window.slope_save_blob) window.slope_save_blob(job.name, blob);
      }
      job.data = [];
      job.state = 3;
    }, function (e) { fail(job, "the video could not be finished: " + (e && e.message || e)); });
  }
  // the canvas a picture of another size is fitted on (and the window's picture is taken with)
  var fitter = null;
  function fitCanvas(w, h) {
    if (!fitter) fitter = typeof OffscreenCanvas === "function" ? new OffscreenCanvas(w, h) : document.createElement("canvas");
    if (fitter.width !== w) fitter.width = w;
    if (fitter.height !== h) fitter.height = h;
    return fitter;
  }

  window.slope_video_jobs = jobs;
  miniquad_add_plugin({
    name: "slope_video",
    version: 1,
    register_plugin: function (importObject) {
      const text = (at, len) => new TextDecoder().decode(new Uint8Array(wasm_memory.buffer, at, len));
      importObject.env.slope_video_start = function (w, h, fps, bitrate, sound, hardware, name, nameLen) {
        if (!canVideo) {
          lastReason = "this browser cannot make videos (it has no video encoder for pages: a current Chrome, Edge, Firefox or Safari has one)";
          return 0;
        }
        var id = next++;
        var job = { id: id, spec: { w: w, h: h, fps: fps, bitrate: bitrate, sound: sound !== 0, hardware: hardware !== 0 }, name: text(name, nameLen),
                    state: 0, reason: "", note: "", codecs: "", written: 0, data: [], bytes: 0, video: null, audio: null, early: [], lastKey: -1, closing: false, size: 0 };
        jobs.set(id, job);
        begin(job);
        return id;
      };
      importObject.env.slope_video_reason = function (id, buf, cap) {
        var job = jobs.get(id);
        var why = id === 0 ? lastReason : job ? (job.state === 4 ? job.reason : [job.codecs, job.note].filter(Boolean).join("; ")) : "";
        var bytes = new TextEncoder().encode(why);
        if (cap >= bytes.length && bytes.length > 0) new Uint8Array(wasm_memory.buffer, buf, bytes.length).set(bytes);
        return bytes.length;
      };
      // ready for another picture: the encoders are picked and not far behind (a failed video is
      // ready too, so that the game hears of it)
      importObject.env.slope_video_room = function (id) {
        var job = jobs.get(id);
        if (!job || job.state === 4) return 1;
        if (job.state !== 1) return 0;
        return job.venc.encodeQueueSize < 3 && (!job.aenc || job.aenc.encodeQueueSize < 16) ? 1 : 0;
      };
      // a picture from the game's memory: four bytes a pixel, the bottom row first
      importObject.env.slope_video_picture = function (id, at, len, w, h, index) {
        var job = jobs.get(id);
        if (!job || job.state === 4) return -1;
        if (job.state > 1 || len < w * h * 4) return 0;
        var src = new Uint8Array(wasm_memory.buffer, at, w * h * 4), rows = new Uint8Array(w * h * 4), row = w * 4;
        for (var y = 0; y < h; y++) rows.set(src.subarray((h - 1 - y) * row, (h - y) * row), y * row);
        var s = job.spec, ts = Math.round(index * 1e6 / s.fps);
        var make = function () {
          var frame;
          try {
            if (w === s.w && h === s.h) {
              frame = new VideoFrame(rows, { format: "RGBA", codedWidth: w, codedHeight: h, timestamp: ts, duration: Math.round(1e6 / s.fps) });
            } else {
              var c = fitCanvas(s.w, s.h), g = c.getContext("2d");
              var tmp = typeof OffscreenCanvas === "function" ? new OffscreenCanvas(w, h) : document.createElement("canvas");
              tmp.width = w; tmp.height = h;
              tmp.getContext("2d").putImageData(new ImageData(new Uint8ClampedArray(rows.buffer), w, h), 0, 0);
              g.drawImage(tmp, 0, 0, s.w, s.h);
              frame = new VideoFrame(c, { timestamp: ts, duration: Math.round(1e6 / s.fps) });
            }
          } catch (e) { return fail(job, "a picture could not be made: " + e.message); }
          encodeFrame(job, frame, index);
        };
        if (job.state === 0) job.early.push(make); else make();
        return 0;
      };
      // the page's canvas as it is now (the game has just drawn it): a recording's picture.
      // 1 if it was taken, 0 if the encoder is behind (it is left out)
      importObject.env.slope_video_canvas = function (id, index) {
        var job = jobs.get(id);
        if (!job || job.state === 4) return -1;
        if (job.state !== 1 || job.venc.encodeQueueSize >= 6) return 0;
        var s = job.spec;
        try {
          var c = fitCanvas(s.w, s.h);
          c.getContext("2d").drawImage(document.getElementById("glcanvas"), 0, 0, s.w, s.h);
          encodeFrame(job, new VideoFrame(c, { timestamp: Math.round(index * 1e6 / s.fps), duration: Math.round(1e6 / s.fps) }), index);
        } catch (e) { fail(job, "the window's picture could not be taken: " + e.message); return -1; }
        return 1;
      };
      // more of the sound: 44100 samples a second, left and right by turns
      importObject.env.slope_video_sound = function (id, at, frames) {
        var job = jobs.get(id);
        if (!job || job.state === 4) return -1;
        if (frames <= 0 || job.state > 1) return 0;
        var pcm = new Int16Array(wasm_memory.buffer, at, frames * 2).slice();
        var make = function () {
          if (!job.aenc) return;
          var rate = job.inRate, data = pcm, n = frames;
          if (rate !== 44100) {
            // (an encoder that only takes 48000 a second: each new sample from the two around it)
            n = Math.floor(frames * rate / 44100);
            data = new Int16Array(n * 2);
            for (var i = 0; i < n; i++) {
              var p = i * 44100 / rate, a = Math.min(Math.floor(p), frames - 1), b = Math.min(a + 1, frames - 1), f = p - a;
              data[i * 2] = pcm[a * 2] + (pcm[b * 2] - pcm[a * 2]) * f;
              data[i * 2 + 1] = pcm[a * 2 + 1] + (pcm[b * 2 + 1] - pcm[a * 2 + 1]) * f;
            }
          }
          if (n <= 0) return;
          job.heard = job.heard || 0;
          try {
            var ad = new AudioData({ format: "s16", sampleRate: rate, numberOfFrames: n, numberOfChannels: 2, timestamp: Math.round(job.heard * 1e6 / rate), data: data });
            job.heard += n;
            job.aenc.encode(ad);
            ad.close();
          } catch (e) { job.aenc = null; job.audio = null; job.note = "no sound: " + e.message; }
        };
        if (job.state === 0) job.early.push(make); else make();
        return 0;
      };
      importObject.env.slope_video_written = function (id) { var job = jobs.get(id); return job ? job.written : 0; };
      importObject.env.slope_video_state = function (id) {
        var job = jobs.get(id);
        if (!job) return 3;
        return job.state === 3 ? 1 : job.state === 4 ? 2 : job.state === 5 ? 3 : 0;
      };
      importObject.env.slope_video_close = function (id) { var job = jobs.get(id); if (job) finish(job); };
      importObject.env.slope_video_cancel = function (id) {
        var job = jobs.get(id);
        if (!job) return;
        try { if (job.venc && job.venc.state !== "closed") job.venc.close(); } catch (e) {}
        try { if (job.aenc && job.aenc.state !== "closed") job.aenc.close(); } catch (e) {}
        job.data = [];
        job.state = 5;
      };
      importObject.env.slope_video_name = function (id, at, len) { var job = jobs.get(id); if (job) job.name = text(at, len); };
      // (a video that is done with is forgotten)
      importObject.env.slope_video_forget = function (id) { jobs.delete(id); };
    }
  });
})();
