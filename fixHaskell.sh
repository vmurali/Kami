#!/bin/bash

mkdir -p Haskell

includes=""

[[ -z $1 ]] || includes="-i$1"

cmd="ghc $includes $1/FixLits.hs -o fixlits"

echo $cmd

$cmd

echo "Fixing Literals"
for file in $(find . -maxdepth 1 -name "*.hs")
do
  ./fixlits $file
  mv $file Haskell
  echo "$file fixed."
done



echo "Adding missing imports"

unameOut="$(uname -s)"
case "${unameOut}" in
  Darwin*) SED=gsed;;
  *)       SED=sed
esac

for file in $(grep -l "CustomExtract" Haskell/*.hs)
do
  grep -q "import qualified CustomExtract" $file
  if [ $? -ne 0 ]
  then
    $SED -i -e '0,/^import/{s/^import/import qualified CustomExtract\nimport/}' $file
  fi
done

for file in $(grep -l "Data\.Char" Haskell/*.hs)
do
  grep -q "import qualified Data\.Char" $file
  if [ $? -ne 0 ]
  then
    $SED -i -e '0,/^import/{s/^import/import qualified Data.Char\nimport/}' $file
  fi
done

for file in $(grep -l "Data\.Bits" Haskell/*.hs)
do
  grep -q "import qualified Data\.Bits" $file
  if [ $? -ne 0 ]
  then
    $SED -i -e '0,/^import/{s/^import/import qualified Data.Bits\nimport/}' $file
  fi
done

for file in $(grep -l "Data\.List" Haskell/*.hs)
do
  grep -q "import qualified Data\.List" $file
  if [ $? -ne 0 ]
  then
    $SED -i -e '0,/^import/{s/^import/import qualified Data.List\nimport/}' $file
  fi
done
