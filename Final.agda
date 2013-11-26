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
  
  data prefix : Set where
    yotta : prefix
    zetta : prefix
    exa   : prefix
    peta  : prefix
    tera  : prefix
    giga  : prefix
    mega  : prefix
    kilo  : prefix
    hecto : prefix
    deca  : prefix
    deci  : prefix
    centi : prefix
    milli : prefix
    micro : prefix
    nano  : prefix
    pico  : prefix
    femto : prefix
    atto  : prefix
    zepto : prefix
    yocto : prefix
    
  data Units : Set where
    noU     : Units
    meter   : Units
    gram    : Units
    second  : Units
    ampere  : Units
    kelvin  : Units
    candela : Units
    mol     : Units
    _u×_    : Units → Units → Units
    _^-1    : Units → Units

  data Imperial : Set where
    foot   : Imperial
    pound  : Imperial


  listUtoU : List Units → Units
  listUtoU [] = noU
  listUtoU (x :: xs) = x u× listUtoU xs

  checkEqual : Units → Units → Bool
  checkEqual noU noU = True
  checkEqual meter meter = True
  checkEqual gram gram = True
  checkEqual second second = True
  checkEqual ampere ampere = True
  checkEqual kelvin kelvin = True
  checkEqual candela candela = True
  checkEqual mol mol = True
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
    `+ : (u1 : Units) → (u2 : Units) → ExpU u2 → u1 == u2 → ExpU u2
    `- : (u1 : Units) → (u2 : Units) → ExpU u2 → u1 == u2 → ExpU u2
    `× : (u1 : Units) → (u2 : Units) → ExpU u2 → ExpU (reduce (u1 u× u2))
    `÷ : (u1 : Units) → (u2 : Units) → ExpU u2 → ExpU (reduce (u1 u× u2 ^-1))

  data UF : Set where
    _of_ : Float → Units → UF

  data UFI : Set where
    _of_ : Float → Imperial → UFI

  data Metric : Set where
    _◂_ : prefix → Units → Metric   --\t
  
  data pUF : Set where
    _of_ : Float → Metric → pUF
  ttt : Float
  ttt = 1.0e−1

  prefixed : (u : pUF) → UF
  prefixed (v of (yotta ◂ u)) = primFloatTimes v 1.0e24 of u
  prefixed (v of (zetta ◂ u)) = primFloatTimes v 1.0e21 of u
  prefixed (v of (exa ◂ u)) = primFloatTimes v 1.0e18 of u
  prefixed (v of (peta ◂ u)) = primFloatTimes v 1.0e15 of u
  prefixed (v of (tera ◂ u)) = primFloatTimes v 1.0e12 of u
  prefixed (v of (giga ◂ u)) = primFloatTimes v 1.0e9 of u
  prefixed (v of (mega ◂ u)) = primFloatTimes v 1000000.0 of u
  prefixed (v of (kilo ◂ u)) = primFloatTimes v 1000.0 of u
  prefixed (v of (hecto ◂ u)) = primFloatTimes v 100.0 of u
  prefixed (v of (deca ◂ u)) = primFloatTimes v 10.0 of u
  prefixed (v of (deci ◂ u)) = primFloatTimes v (primFloatMinus 0.0 10.0) of u
  prefixed (v of (centi ◂ u)) = primFloatTimes v (primFloatMinus 0.0 100.0) of u
  prefixed (v of (milli ◂ u)) = primFloatTimes v (primFloatMinus 0.0 1000.0) of u
  prefixed (v of (micro ◂ u)) = primFloatTimes v (primFloatMinus 0.0 1000000.0) of u
  prefixed (v of (nano ◂ u)) = primFloatTimes v (primFloatMinus 0.0 1.0e9) of u
  prefixed (v of (pico ◂ u)) = primFloatTimes v (primFloatMinus 0.0 1.0e12) of u
  prefixed (v of (femto ◂ u)) = primFloatTimes v (primFloatMinus 0.0 1.0e15) of u
  prefixed (v of (atto ◂ u)) = primFloatTimes v (primFloatMinus 0.0 1.0e18) of u
  prefixed (v of (zepto ◂ u)) = primFloatTimes v (primFloatMinus 0.0 1.0e21) of u
  prefixed (v of (yocto ◂ u)) = primFloatTimes v (primFloatMinus 0.0 1.0e24) of u


  Imp-to-SI : (x : UFI) → UF
  Imp-to-SI (v of foot) = primFloatTimes v 0.3048 of meter
  Imp-to-SI (v of pound) = primFloatTimes v 453.592 of gram

  val : UF → Float
  val (f of u) = f 

  uns : UF → Units
  uns (f of u) = u

  data Exp : UF → Set where
    V    : (u : UF) → Exp u
    `+ : (x : UF) → (y : UF) → Exp y → (uns x == uns y) → Exp ((primFloatPlus (val x) (val y)) of (uns y))
    `- : (x : UF) → (y : UF) → Exp y → (uns x == uns y) → Exp ((primFloatMinus (val x) (val y)) of (uns y))
    `× : (x : UF) → (y : UF) → Exp y → Exp ((primFloatTimes (val x) (val y)) of (reduce((uns x) u× (uns y))))
    `÷ : (x : UF) → (y : UF) → Exp y → Exp ((primFloatDiv (val x) (val y)) of (reduce ((uns x) u× (uns y) ^-1)))

  test : UF
  test = 1.0 of noU

  test5 : Exp (1.0 of noU)
  test5 = V test
  
  test+ : Exp (2.0 of noU)
  test+ = `+ test test (V test) Refl 
  
  meter1 : UF
  meter1 = 2.5 of meter
  meter2 : UF
  meter2 = 1.0 of meter

  test- : Exp (1.5 of meter)
  test- = `- meter1 meter2 (V meter2) Refl
  
  second1 : UF
  second1 = 2.0 of second
  second2 : UF
  second2 = 2.5 of second

 -- test× : Exp (5.0 of second)
 -- test× = ``× {!second1!} second2 (V second2)

  --test×2 : Exp (1.0 of (meter u× second ^-1))
  --test×2 = `÷ {!meter1!} second2 (V second2)

  d1 : UF
  d1 = 30.0 of meter
  d2 : UF
  d2 = 10.0 of meter
  ac : UF
  ac = 5.0 of ((meter u× (second ^-1)) u× (second ^-1))
  t : UF
  t = 0.828427 of second
  vi : UF
  vi = 20.0 of (meter u× second ^-1)

  test6 : Exp (30.0 of meter)
  test6 = {!(V d2) `+ (((V vi) `× (V t)) `+ ((V ac) `× ((V t) `× (V t))))!}

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