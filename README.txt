This formalization has been checked with the parametric branch of the
Agda proof assistant.

The sources are available from github

  git clone https://github.com/agda/agda.git
  cd agda
  git checkout parametric

Some basics are explained in

  README.agda

EXAMPLES FROM THE INTRODUCTORY PAPER
====================================

The examples below come from the paper that introduced the type system:

  Andreas Nuyts, Andrea Vezzosi, and Dominique Devriese. Parametric quantifiers for dependent type theory. Proceedings
of the ACM on Programming Languages, 1, September 2017. Issue ICFP, Accepted.

Section 2 corresponds to the file

  IntroExample.agda

Section 4.1 "Church and co-Church encoded data types" refers to the files

  Church/InitialAlgebras.agda
  Church/InitialAlgebrasCont.agda
  Church/FinalColgebras.agda

 using

  Graph/Source.agda
  Graph/Target.agda

Section 4.2 "Sized types" refers to the files

  ParamSize.agda
  SizeAlgebras.agda
  SizeCoAlgebras.agda
