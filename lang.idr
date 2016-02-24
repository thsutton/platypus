module Main

data Nt : Type where
  Zn : Nt
  Sn : Nt -> Nt

mutual
  data Even : Nt -> Type where
    EvenZn : Even Zn
    EvenSn : Odd n -> Even (Sn n)

  data Odd : Nt -> Type where
    OddSn : Even n -> Odd (Sn n)

data Add : Nt -> Nt -> Nt -> Type where
  AddZn : Add Zn n n

  AddSn : Add n1 n2 n3 -> Add (Sn n1) n2 (Sn n3)

data St : Type where
  Empty : St

data Concat : St -> St -> St -> Type where
  ConcatE_L : Concat Empty s s
  ConcatE_R : Concat s Empty s

data Length : St -> Nt -> Type where
  LengthE : Length Empty Zn

svAB : (a : Nt) -> (b : Nt) -> { auto prf : Add a b c} -> Add a b c
svAB _ _ { prf } = prf

svAC : (a : Nt) -> (c : Nt) -> { auto prf : Add a b c} -> Add a b c
svAC _ _ { prf } = prf

svBC : (b : Nt) -> (c : Nt) -> { auto prf : Add a b c} -> Add a b c
svBC _ _ { prf } = prf

data E : Type where
  Num : Nt -> E
  Str : St -> E
  Plus : E -> E -> E
  Cat : E -> E -> E
  Len : E -> E
  Let : E -> (E -> E) -> E

data Ty : Type where
  NumTy : Ty
  StrTy : Ty

data Typing : E -> Ty -> Type where
  TypeNum : Typing (Num n) NumTy
  TypeStr : Typing (Str n) StrTy

  TypePlus : Typing n NumTy -> Typing m NumTy -> Typing (Plus n m) NumTy
  TypeCat  : Typing n StrTy -> Typing m StrTy -> Typing (Cat n m) StrTy
  TypeLen  : Typing s StrTy -> Typing (Len s) NumTy

  TypeLet  : Typing e1 t1
          -> {auto d : ((x: E) -> Typing x t1 -> Typing (e2 x) t2)}
          -> Typing (Let e1 e2) t2

%hint
typeOf : (e : E) -> { auto prf : Typing e t } -> Typing e t
typeOf _ { prf } = prf

data Val : E -> Type where
  ValNum : (n : Nt) -> Val (Num n)
  ValStr : (s : St) -> Val (Str s)

data Eval : E -> E -> Type where
  EvalVal    : Val v -> Eval v v

  EvalPlus  : Eval n1 n2 -> Eval m1 m2 -> Eval (Plus m1 n1) (Plus m2 n2)

  EvalCar   : Eval s1 (Str s2) -> Eval t1 (Str t2) -> Concat s2 t2 r
           -> Eval (Cat s1 t1) (Str r)

  EvalLen   : Length s2 n -> Eval s1 (Str s2) -> Eval (Len s1) (Num n)

  EvalLet   : Eval e1 e2 -> Eval (v e2) r -> Eval (Let e v) r

eval : (e : E) -> {auto prf : Eval e e1} -> Eval e e1
eval _ { prf } = prf
