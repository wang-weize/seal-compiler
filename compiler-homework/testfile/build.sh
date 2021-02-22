#!/bin/bash
script=$1
cp -f $script lexer
echo "--------Test" $script "--------"
i=1
for filename in *.seal; do
    echo "------NO $i --- using" $filename "--------"
    ./lexer $filename > tempfile
    diff tempfile answer/$filename.out
    if [ $? -eq 0 ] ; then
        echo -e "\033[32m passed \033[0m"
    else
        echo -e "\033[31m difference occured! \033[0m" 
    fi
    rm -f tempfile
    let 'i+=1'
done
