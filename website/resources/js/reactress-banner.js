


var images = [
	"event0",
	"event1",
	"event2",
	"event3",
	"event4",
	"event5",
	"event6",
	"event7",
	"event8",
	"event9",
	"event10",
	"event11",
	"event12",
	"event13",
	"event14",
	"event15",
	"event16",
	"event16",
	"event17",
	"event18",
	"event19",
	"event20",
	"event21",
	"event22"
];

function createEvent() {
	var bannercenter = document.getElementById("bannercenter");
	var ev = document.createElement("img");
	var distance = 0.5 + 0.5 * Math.random();
	var length = 160 * distance;
	var pathtop = 20;
	var left = Math.floor(50 - distance * 40 + 2 * distance * 40 * Math.random());
	var height = Math.floor(36 * distance);
	var imagename = images[Math.floor(Math.random() * images.length)];
	var css = "position: absolute; " +
	"top: " + (pathtop + length) + "px; " +
	"left: calc(" + left + "% + 200px);" +
	"height: " + height + "px;" +
	"opacity: 0.0;";
	ev.setAttribute("style", css);
	ev.setAttribute("src", "/resources/images/icons/" + imagename + ".png");
	bannercenter.appendChild(ev);

	function onComplete() {
		setTimeout(createEvent, Math.floor(1000 + 3000 * Math.random()));
		bannercenter.removeChild(ev);
	}

	var time = 800 + 800 * Math.random();

	createjs.Tween.get(ev)
      .to({top: pathtop + 0.5 * length, opacity: 0.8}, time, createjs.Ease.quadIn)
      .to({top: pathtop + 0.0 * length, opacity: 0.0}, time, createjs.Ease.quadOut)
      .call(onComplete);
}


createjs.CSSPlugin.install(createjs.Tween);
createjs.Ticker.setFPS(30);

setTimeout(createEvent, 1000);
setTimeout(createEvent, 1500);
setTimeout(createEvent, 2500);
setTimeout(createEvent, 4000);
