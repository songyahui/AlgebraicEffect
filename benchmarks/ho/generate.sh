#!/bin/bash

# Someday https://github.com/realworldocaml/mdx/issues/245

for f in src/examples/{iter.ml,closure.ml,map.ml,fold.ml,compose.ml,applyN.ml,all.ml,exception.ml}; do
  echo "
\`\`\`sh
\$ DEBUG=0 hyperfine --warmup 2 'dune exec parsing/hip.exe $f'
\$ loc $f

\$ rg --multiline --multiline-dotall '(\*@.*?@\*)' $f

\$ rg --multiline --multiline-dotall -c '(\*@.*?@\*)' $f

\$ rg --multiline --multiline-dotall '(\*@.*?@\*)' $f | wc -l
\`\`\`"
done