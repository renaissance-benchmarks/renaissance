"use strict";


class Log {
  static error(msg, err) {
    console.log(msg);
    throw new Error(err);
  }
}


class UidGenerator {
  constructor() {
    this.count = 0;
    this.labelCounts = {};
  }

  num() {
    return this.count++;
  }

  labelNum(label) {
    if (!(label in this.labelCounts)) {
      this.labelCounts[label] = 0;
    }
    return this.labelCounts[label]++;
  }
}


class Dict {
  static ensure(obj, k, v) {
    if (!(k in obj)) {
      obj[k] = v;
    }
    return obj[k];
  }
}


var Uid = new UidGenerator();
