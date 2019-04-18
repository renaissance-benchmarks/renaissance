

function loadRemoteContent(elementId, url, logoname, kind) {
  var element = document.getElementById(elementId);
  $.get(url, function(data) {
    if (kind == "license") {
      var icon = document.createElement("img");
      icon.setAttribute("src", "/resources/images/" + logoname);
      icon.setAttribute("height", 38);
      var title = document.createElement("span")
      title.innerText = "Renaissance";
      title.setAttribute("style", "font-size: 36px; vertical-align: bottom; padding-left: 8px;")
      var contentText = window.atob(data.content);
      contentText = contentText.replace(/\t/g, '    ').replace(/  /g, '&nbsp; ').replace(/  /g, ' &nbsp;').replace(/\r\n|\n|\r/g, '<br />');
      element.appendChild(icon);
      element.appendChild(title);
      element.innerHTML = element.innerHTML + '<br/>' + contentText;
    } else if (kind == "markdown") {
      var contentMarkdown = window.atob(data.content);
      var renderedMarkdown = marked(contentMarkdown);
      element.innerHTML = element.innerHTML + '<br/>' + renderedMarkdown;
    }
  });
}
