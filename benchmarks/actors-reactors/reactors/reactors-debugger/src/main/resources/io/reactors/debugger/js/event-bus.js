"use-strict";


class EventBus {
  constructor() {
    this.observers = {}
    this.uidCount = 0;
  }

  emit() {
    var tpe = arguments[0];
    var rest = Array.prototype.slice.call(arguments, 1);
    if (this.observers[tpe]) {
      var tpeObservers = this.observers[tpe];
      for (var uid in tpeObservers) {
        var obs = tpeObservers[uid];
        obs.apply(null, rest);
      }
    }
  }

  generateUid() {
    return this.uidCount++;
  }

  observe(tpe, f) {
    if (!(tpe in this.observers)) {
      this.observers[tpe] = {};
    }
    var uid = this.generateUid();
    this.observers[tpe][uid] = f;

    () => delete this.observers[tpe][uid];
  }
}


var eventBus = new EventBus();
