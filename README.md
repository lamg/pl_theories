# Programming Language Theories

[![Lean][Lean Shield]][Lean Site]
[![License][License Shield]][License File]
[![CI][CI Shield]][CI Actions]

Small ML-like language being specified and implemented in Lean, with focus on theories for:

- [ ] syntax parsing
- [ ] type checking (Algorithm W)
- [ ] semantics (Big Step)

## Read the series

The published site is at [lamg.dev/pl_theories](https://lamg.dev/pl_theories/).
It is generated from the Lean sources with Verso, so the explanations,
examples, and proofs stay together.

Read the typechecking chapters in order: basic concepts, unification,
then Algorithm W. Executable type inference is still under development.

## Build and preview

```sh
lake build PlTheories
lake query :literateHtml
python3 -m http.server 8000 --directory .lake/build/literate-html
```

Open <http://localhost:8000/>. The first site build compiles Verso and can
take several minutes. `literate.toml` controls the chapter order, page titles,
and rendering of explanatory docstrings as prose. `styles/reading.css` supplies
the device-aware light/dark reading theme. When changing only CSS locally,
remove `.lake/build/literate-html.trace` before rebuilding; deployment does
this automatically because Verso 4.35 does not track extra CSS contents.

## Publishing

GitHub Actions builds the site on pull requests and publishes pushes to
`master` through the `github-pages` environment. Pages must use **GitHub
Actions** as its source. The dependency versions are pinned in
`lake-manifest.json`.

This project inherits `lamg.dev` from the account's user site and is served
under `/pl_theories/`. Do not add a project-specific `CNAME` for the apex
domain. Verso generates relative asset and navigation URLs for subpath hosting.

[CI Actions]: https://github.com/lamg/pl_theories/actions/workflows/lean_action_ci.yml
[CI Shield]: https://img.shields.io/github/actions/workflow/status/lamg/pl_theories/lean_action_ci.yml?style=flat-square&label=CI
[Lean Site]: https://lean-lang.org/
[Lean Shield]: https://img.shields.io/badge/Lean-v4.35.0-blue?style=flat-square
[License File]: LICENSE
[License Shield]: https://img.shields.io/badge/License-Apache--2.0-blue?style=flat-square
