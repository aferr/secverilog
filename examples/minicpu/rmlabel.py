#!/usr/bin/python

import os
import re

os.chdir("./")
abs = "./no_label/"

for files in os.listdir("."):
    if files.endswith(".v"):
        f = open( files, 'r')
        new_file = open( abs + files, 'w' )
        for line in f:
            line = re.sub(r"\{(L|H|BusPar.*|Way.*|Par ReadLabel)\}", "", line)
            new_file.write( line )
        new_file.close()
        f.close()
        
