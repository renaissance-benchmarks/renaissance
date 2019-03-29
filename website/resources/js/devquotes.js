---
---

Date.prototype.getDOY = function() {
	var onejan = new Date(this.getFullYear(),0,1);
	return Math.ceil((this - onejan) / 86400000);
}

function fetchQuote() {
	var quotes = {% include devquotes.json %};
	var today = new Date();
	var day = today.getDOY() + 2;
	var index = day % quotes.length;
	return quotes[index];
}
