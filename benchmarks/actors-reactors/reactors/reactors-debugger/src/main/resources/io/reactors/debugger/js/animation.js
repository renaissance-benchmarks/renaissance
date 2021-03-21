"use strict";


class Interpolator {
  map(f) {
    return {
      hasNext: () => {
        return this.hasNext();
      },
      next: () => {
        return f(this.next());
      },
      stop: () => this.stop()
    }
  }
}


class RangeInterpolator extends Interpolator {
  constructor(totalFrames, from, end, func) {
    super();
    this.totalFrames = totalFrames;
    this.from = from;
    this.end = end;
    this.func = func;
    this.frame = 0;
  }

  hasNext() {
    return this.frame < this.totalFrames;
  }

  next() {
    var v = this.func(this.from, this.end, this.frame, this.totalFrames);
    this.frame += 1;
    return v;
  }

  stop() {
    this.frame = this.totalFrames;
  }
}


class LinearInterpolator extends RangeInterpolator {
  constructor(totalFrames, from, end) {
    super(totalFrames, from, end, (from, end, frame, totalFrames) => {
      return from + 1.0 * (end - from) * (frame / totalFrames);
    });
  }
}


class SmoothStepInterpolator extends RangeInterpolator {
  constructor(totalFrames, from, end) {
    super(totalFrames, from, end, (from, end, frame, totalFrames) => {
      var x = 1.0 * frame / totalFrames;
      var factor = x * x * x * (x * (x * 6 - 15) + 10);
      return from + (end - from) * factor;
    });
  }
}


class Animation {
  constructor(interpolator, setter, onStart, onComplete) {
    this.interpolator = interpolator;
    this.setter = setter;
    this.onStart = onStart;
    this.onComplete = onComplete;
  }

  nextFrame() {
    if (this.onStart) {
      this.onStart();
      this.onStart = null;
    }
    if (this.interpolator.hasNext()) {
      var v = this.interpolator.next();
      this.setter(v);
      return true;
    } else {
      this.stop();
      return false;
    }
  }

  stop() {
    this.interpolator.stop();
    if (this.onComplete) {
      this.onComplete();
      this.onComplete = null;
    }
  }
}


class Animator {
  constructor() {
    this.totalAnimations = 0;
    this.maxAnimations = 32;
    this.labeledAnimations = {};
    this.generator = new UidGenerator();
  }

  start(ani) {
    var frame = 0;
    var nextFrame = () => {
      if (ani.nextFrame()) {
        setTimeout(nextFrame, 30);
      }
    };
    nextFrame();
  }

  startBudgeted(ani) {
    if (this.totalAnimations < this.maxAnimations) {
      this.totalAnimations += 1;
      var originalOnComplete = ani.onComplete;
      ani.onComplete = () => {
        this.totalAnimations -= 1;
        if (originalOnComplete) originalOnComplete();
      };
      this.start(ani);
    } else {
      ani.onStart();
      ani.onComplete();
    }
  }

  startLabeled(ani, label, budgeted) {
    var originalOnComplete = ani.onComplete;
    ani.onComplete = () => {
      var currAni = this.labeledAnimations[label];
      if (currAni === ani) {
        delete this.labeledAnimations[label];
        if (originalOnComplete) originalOnComplete();
      }
    }
    if (this.labeledAnimations[label]) {
      this.labeledAnimations[label].stop();
    }
    this.labeledAnimations[label] = ani;
    if (budgeted) {
      this.startBudgeted(ani);
    } else {
      this.start(ani);
    }
  }
}


var animation = {
  linear: (total, from, end, setter, onStart, onComplete) => {
    var i = new LinearInterpolator(total, from, end);
    return new Animation(i, setter, onStart, onComplete);
  },
  smoothstep: (total, from, end, setter, onStart, onComplete) => {
    var i = new SmoothStepInterpolator(total, from, end);
    return new Animation(i, setter, onStart, onComplete);
  }
};
