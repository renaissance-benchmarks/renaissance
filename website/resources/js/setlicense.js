

function setLicense(url, logoname) {
  var licensebox = document.getElementById("licensebox");
  $.get(url, function(data) {
    var icon = document.createElement('IMG');
    icon.setAttribute("src", "/resources/images/" + logoname);
    icon.setAttribute("height", 48);
    var ltxt = window.atob(data.content);
    ltxt = ltxt.replace(/\t/g, '    ').replace(/  /g, '&nbsp; ').replace(/  /g, ' &nbsp;').replace(/\r\n|\n|\r/g, '<br />');
    licensebox.appendChild(icon);
    licensebox.innerHTML = licensebox.innerHTML + '<br/>' + ltxt;
  });
}
