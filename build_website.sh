set -x

rm -rf .lake/build rendered_website
lake exe versowebsite --output rendered_website