#/bin/bash

cat << EOF

The linear algebra contribution for Coq 7.4, 
 by Jasper Stein (jasper@cs.kun.nl)
 extending the "algebra" contribution by Loic Pottier

EOF

REPLY=""
echo Require Export Parts. > dummy.v
coqc dummy.v >/dev/null 2>&1
if [ $? != 0 ]
then echo "Apparently the algebra contribution is not in Coq's default search path."
     echo "Please enter the path to the algebra contribution directory."
     echo "(Either the full path or relative to `pwd`):"
     read
fi

if [[ $REPLY == "" ]]
then INCLUDES=""
else INCLUDES="-I $REPLY"
fi

rm dummy.v dummy.vo >/dev/null 2>&1

echo
echo "Now trying to coq all .v files..."
echo "This step may take a while (some 11 minutes on my PIII/733MHz)"
echo "To track progress, do e.g. tail -f coq.log on another virtual terminal."
echo
coqdep `cat filesInOrder` > .depend 2>/dev/null
coq_makefile `cat filesInOrder` > makefile-tmp
sed s%=-q%"=-I `pwd`/support -I `pwd`/extras -I `pwd`/examples -I `pwd`/LinAlg $INCLUDES"% \
  makefile-tmp > makefile
rm makefile-tmp
make > coq.log 2>&1
if [ $? != 0 ]
then echo "Something went wrong with make. Check coq.log - it may say why."
fi

echo
echo "Trying to make documentation (docu.ps)..."
echo
which coqdoc >/dev/null
if [ $? != 0 ]
then echo "Coqdoc was not found. To generate documentation, please put coqdoc in your PATH"
else coqdoc -s -toc -l -g --latex -o docu.tex --files-from filesInOrder
     echo
     latex docu.tex >/dev/null
     latex docu.tex >/dev/null
     latex docu.tex >/dev/null
     dvips docu.dvi -o docu.ps
     if [[ $? == 0 ]] 
     then DOCUSUCCESS="true"
     fi
fi

echo
echo "That's it. Everything should be installed now."
echo -n "Check Linear_Algebra_by_Friedberg_Insel_Spence.v"
if [[ $DOCUSUCCESS == "true" ]]
then echo " and docu.ps"
else echo
fi
echo "for an overview and starting point to this contribution."
echo
echo "Share and enjoy!"
echo "Jasper Stein"
echo "(jasper@cs.kun.nl)"
echo
