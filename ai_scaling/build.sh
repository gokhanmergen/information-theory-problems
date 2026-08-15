#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd "$DIR"

echo "Compiling theoretical_bounds_on_ai_scaling_laws.tex with tectonic..."
/opt/homebrew/bin/tectonic theoretical_bounds_on_ai_scaling_laws.tex

echo "Build successful! PDF output: $DIR/theoretical_bounds_on_ai_scaling_laws.pdf"
