"use-strict";


class EventStream {
  constructor() {
    this.uidCount = 0;
    this.observers = {};
  }

  observe(f) {
    var uid = this.uidCount++;
    this.observers[uid] = f;
    return () => {
      delete this.observers[uid];
    }
  }

  post() {
    for (var uid in this.observers) {
      var f = this.observers[uid];
      f.apply(this, arguments);
    }
  }
}
