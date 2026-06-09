#!/usr/bin/env bash
# Build paper.pdf from paper.md.
# Requires: pandoc + a LaTeX engine (tectonic recommended) + a Unicode mono
# font that covers the Lean glyphs in the code blocks (JuliaMono recommended:
# it renders R, forall, theta, norm bars, summation, subscripts, etc.).
#
# Static, no-root install used on monkey-01:
#   pandoc:    github.com/jgm/pandoc/releases  -> ~/.local/bin/pandoc
#   tectonic:  github.com/tectonic-typesetting/tectonic/releases (musl) -> ~/.local/bin/tectonic
#   JuliaMono: github.com/cormullion/juliamono/releases -> ~/.local/share/fonts + fc-cache -f
set -euo pipefail

pandoc paper.md -o paper.pdf \
  --pdf-engine=tectonic \
  -V geometry:margin=1in \
  -V colorlinks=true \
  -V monofont="JuliaMono"

echo "built paper.pdf"
