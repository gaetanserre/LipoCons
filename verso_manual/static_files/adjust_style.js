window.addEventListener('load', function () {
  document.querySelectorAll('.has-info, .warning').forEach(function (el) {
    el.classList.remove('has-info', 'warning');

    el.querySelectorAll('span.hover-container').forEach(function (hoverSpan) {
      hoverSpan.remove();
    });
  });

  document.querySelectorAll('p').forEach(function (p) {
    if (p.querySelector('img')) {
      p.setAttribute('align', 'center');
    }
  });
});
