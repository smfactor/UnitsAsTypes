open import lib.Preliminaries

module Final where
  
  postulate
    Int    : Set
    Float  : Set

  {-# BUILTIN INTEGER Int #-}
  {-# BUILTIN FLOAT Float #-}

  primitive
    primFloatPlus    : Float → Float → Float
    primFloatMinus   : Float → Float → Float
    primFloatTimes   : Float → Float → Float
    primFloatDiv     : Float → Float → Float

--  open Nat using (_+_)
  open List using (_++_ ; [_] ; ++-assoc)

  {-  data dim : Set where
      scalar : dim
      length : dim
      mass   : dim
      time   : dim
      _`×_   : dim → dim → dim
      _^-1   : dim → dim
  -}
  {-
  data prefix : Set where
    G : prefix
    M : prefix
    k : prefix
    c : prefix
    m : prefix
    μ : prefix
    O : prefix
  -}  

  data Units : Set where
    noU : Units
    meter   : Units
    gram  : Units
    second   : Units
    _u×_   : Units → Units → Units
    _^-1   : Units → Units


  listUtoU : List Units → Units
  listUtoU [] = noU
  listUtoU (x :: xs) = x u× listUtoU xs

  checkEqual : Units → Units → Bool
  checkEqual noU noU = True
  checkEqual meter meter = True
  checkEqual gram gram = True
  checkEqual second second = True
  checkEqual (x ^-1) (y ^-1) = checkEqual x y
  checkEqual (x1 u× x2) (y1 u× y2) with checkEqual x1 y1
  checkEqual (x1 u× x2) (y1 u× y2) | True with checkEqual x2 y2
  checkEqual (x1 u× x2) (y1 u× y2) | True | True = True
  checkEqual (x1 u× x2) (y1 u× y2) | True | False = False
  checkEqual (x1 u× x2) (y1 u× y2) | False = False
  checkEqual x y = False

  cancelS : Units → List Units → (Bool × List Units)
  cancelS x [] = False , []
  cancelS x (y :: ys) with checkEqual x y
  cancelS x (y :: ys) | True = True , ys
  cancelS x (y :: ys) | False with cancelS x  ys
  cancelS x (y :: ys) | False | True , ys' = True , y :: ys'
  cancelS x (y :: ys) | False | False , ys' = False , y :: ys'

  --cancel should remove all duplicates in the two lists
  cancel : List Units → List Units → (List Units × List Units)
  cancel [] b = [] , b
  cancel (x :: ts) b with cancelS x b
  cancel (x :: ts) b | True , b' = cancel ts b'
  cancel (x :: ts) b | False , _ with cancel ts b
  cancel (x :: ts) b | False , _ | t' , b' = x :: t' , b'


  makeFrac : Units → List Units × List Units
  makeFrac (x ^-1 u× y ^-1) with makeFrac x | makeFrac y
  ... | tx , bx | ty , by = bx ++ by , tx ++ ty
  makeFrac (x ^-1 u× y) with makeFrac x | makeFrac y
  ... | tx , bx | ty , by = bx ++ ty , tx ++ by
  makeFrac (x u× y ^-1) with makeFrac x | makeFrac y
  ... | tx , bx | ty , by = tx ++ by , bx ++ ty
  makeFrac (x u× y) with makeFrac x | makeFrac y
  ... | tx , bx | ty , by = tx ++ ty , bx ++ by
  makeFrac (x ^-1) with makeFrac x 
  ... | t , b = b , t
  makeFrac x = x :: [] , noU :: []

  reduce : Units → Units 
  reduce x with makeFrac x
  reduce x | t , b with cancel t b
  reduce x | t , b | t' , [] = listUtoU t'
  reduce x | t , b | t' , b' = listUtoU t' u× (listUtoU b' ^-1)

  v : Units
  v = (meter u× (meter ^-1))

  test1 : makeFrac v == (meter :: noU :: [] , noU :: meter :: [])
  test1 = Refl

  test2 : cancel (meter :: noU :: []) (noU :: meter :: []) == ([] , [])
  test2 = Refl

  test3 : listUtoU [] == noU

  test3 = Refl
  test4 : listUtoU [] u× (listUtoU [] ^-1) == noU u× (noU ^-1)
  test4 = Refl

  --  testf1 : reduce v == (noU u× (noU ^-1))
  --  testf1 = Refl
    
  testf : reduce v == noU
  testf = Refl 

  data ExpU : Units → Set where
    lift : (u : Units) → ExpU u
    _`+_ : (u1 : Units) → (u2 : Units) → ExpU u2 → u1 == u2 → ExpU u2
    _`-_ : (u1 : Units) → (u2 : Units) → ExpU u2 → u1 == u2 → ExpU u2
    _`×_ : (u1 : Units) → (u2 : Units) → ExpU u2 → ExpU (reduce (u1 u× u2))
    _`÷_ : (u1 : Units) → (u2 : Units) → ExpU u2 → ExpU (reduce (u1 u× u2 ^-1))

  data UF : Set where
    _of_ : Float → Units → UF

  val : UF → Float
  val (f of u) = f 

  uns : UF → Units
  uns (f of u) = u

  data Exp : UF → Set where
    V    : (u : UF) → Exp u
    _`+_ : (x : UF) → (y : UF) → Exp y → (uns x == uns y) → Exp ((primFloatPlus (val x) (val y)) of (uns y))
    _`-_ : (x : UF) → (y : UF) → Exp y → (uns x == uns y) → Exp ((primFloatMinus (val x) (val y)) of (uns y))
    _`×_ : (x : UF) → (y : UF) → Exp y → Exp ((primFloatTimes (val x) (val y)) of ((uns x) u× (uns y)))
    _`÷_ : (x : UF) → (y : UF) → Exp y → Exp ((primFloatDiv (val x) (val y)) of ((uns x) u× (uns y) ^-1))


  test : UF
  test = 1.0 of noU
 
    
  test-e-1 : {uf : UF} → Exp uf
  test-e-1 {uf} = V uf
 {-
    cancel (noU , noU) = noU
    cancel (noU , meter) = meter ^-1
    cancel (noU , gram) = gram ^-1
    cancel (noU , second) = second  ^-1
    cancel (noU , b u× b1) = b u× b1
    cancel (noU , b ^-1) = b
    cancel (meter , noU) = meter
    cancel (meter , meter) = noU
    cancel (meter , gram) = meter u× (gram ^-1)
    cancel (meter , second) = meter u× (second ^-1)
    cancel (meter , b u× b1) = {!!}
    cancel (meter , b ^-1) = {!!}
    cancel (gram , noU) = gram
    cancel (gram , meter) = gram u× (meter ^-1)
    cancel (gram , gram) = noU
    cancel (gram , second) = gram u× (second ^-1)
    cancel (gram , b u× b1) = {!!}
    cancel (gram , b ^-1) = {!!}
    cancel (second , noU) = second
    cancel (second , meter) = second u× (meter ^-1)
    cancel (second , gram) = second u× (gram ^-1)
    cancel (second , second) = noU
    cancel (second , b u× b1) = {!!}
    cancel (second , b ^-1) = {!!}
    cancel (t u× t1 , noU) = t u× t1
    cancel (t u× t1 , meter) = {!!}
    cancel (t u× t1 , gram) = {!!}
    cancel (t u× t1 , second) = {!!}
    cancel (t u× t1 , b u× b1) = {!!}
    cancel (t u× t1 , b ^-1) = {!!}
    cancel (t ^-1 , noU) = {!!}
    cancel (t ^-1 , meter) = {!!}
    cancel (t ^-1 , gram) = {!!}
    cancel (t ^-1 , second) = {!!}
    cancel (t ^-1 , b u× b1) = {!!}
    cancel (t ^-1 , b ^-1) = {!!}
  -}