document.addEventListener("DOMContentLoaded", function () {
  const codes = document.querySelectorAll("code.hl.lean.block");

  codes.forEach(code => {
    const spans = Array.from(code.children);

    const onlyEmptySpans = spans.length > 0 && spans.every(span =>
      span.tagName === "SPAN" && span.textContent.trim() === ""
    );

    if (onlyEmptySpans) {
      code.remove();
    }
  });
});

document.addEventListener("DOMContentLoaded", function () {
  const nav = document.querySelector("nav.top");
  if (!nav) return;

  const ol = nav.querySelector("ol");
  if (!ol) return;

  const ul = document.createElement("ul");

  for (let attr of ol.attributes) {
    ul.setAttribute(attr.name, attr.value);
  }

  while (ol.firstChild) {
    ul.appendChild(ol.firstChild);
  }

  nav.replaceChild(ul, ol);
});

window.onload = function () {
  document.body.style.display = 'block';
};
