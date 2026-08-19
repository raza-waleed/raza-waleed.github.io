(function () {
  var scroller = document.querySelector('[data-method-scroller]');
  if (!scroller || !('IntersectionObserver' in window)) return;

  var steps = scroller.querySelectorAll('[data-method-step]');
  var stages = scroller.querySelectorAll('[data-stage]');
  var dots = scroller.querySelectorAll('[data-step-dot]');
  var currentLabel = scroller.querySelector('[data-method-current]');
  var nameLabel = scroller.querySelector('[data-method-name]');

  var names = {};
  steps.forEach(function (step) {
    var heading = step.querySelector('h4');
    if (heading) names[step.getAttribute('data-method-step')] = heading.textContent;
  });

  function activate(n) {
    steps.forEach(function (el) {
      el.classList.toggle('is-active', el.getAttribute('data-method-step') === n);
    });
    stages.forEach(function (el) {
      el.classList.toggle('is-active', el.getAttribute('data-stage') === n);
    });
    dots.forEach(function (el) {
      el.classList.toggle('is-active', el.getAttribute('data-step-dot') === n);
    });
    if (currentLabel) currentLabel.textContent = '0' + n;
    if (nameLabel && names[n]) nameLabel.textContent = names[n];
  }

  var io = new IntersectionObserver(function (entries) {
    entries.forEach(function (entry) {
      if (entry.isIntersecting) activate(entry.target.getAttribute('data-method-step'));
    });
  }, { rootMargin: '-45% 0px -45% 0px', threshold: 0 });

  steps.forEach(function (step) { io.observe(step); });
})();
