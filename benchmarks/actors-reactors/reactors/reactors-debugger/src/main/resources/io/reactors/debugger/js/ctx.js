
class Ctx {
  constructor() {
    this._graph = null;
    this.animator = new Animator();
  }

  getReactorCoordinates(id) {
    if (this._graph) return this._graph.getReactorCoordinates(id);
    else return undefined;
  }
}
