#!/bin/bash

if [ -f parse.hh ]; then
    mv parse.hh parse.h && sed -i 's/parse.hh/parse.h/g' parse.cc
elif [ -f parse.cc.h ]; then
    mv parse.cc.h parse.h && sed -i 's/parse.cc.h/parse.h/g' parse.cc
elif [ -f parse.h ]; then
    echo ''
else
    echo 'no header file found?'
fi
