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

  data ExpU : Units → Set where
    lift : (u : Units) → ExpU u
    _`+_ : (u1 : Units) → (u2 : Units) → ExpU u2 → u1 == u2 → ExpU u2
    _`-_ : (u1 : Units) → (u2 : Units) → ExpU u2 → u1 == u2 → ExpU u2
    _`×_ : (u1 : Units) → (u2 : Units) → ExpU u2 → ExpU (u1 u× u2)
    _`÷_ : (u1 : Units) → (u2 : Units) → ExpU u2 → ExpU (u1 u× u2 ^-1)

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
   
  --  _`×_ : {u₁ u₂ : ExpU} → (ExpU u₁) → (ExpU u₂) → ExpU (u₁ u× u₂)
  --  _`÷_ : {u₁ u₂ : ExpU} → (ExpU u₁) → (ExpU u₂) → ExpU (u₁ u× (u₂ ^-1))

 -- u-test : ExpU ((meter u× second ^-1) u× gram)
--  u-test = {!((lift meter) `÷ (lift second)) u× gram!}

{-
  Val : Units → Float
  Val (noU x) = x
  Val (meter x) = x
  Val (gram x) = x
  Val (second x) = x
  Val (x u× y) = primFloatTimes (Val x) (Val y)
  Val (x ^-1) = primFloatDiv 1.0 (Val x)

  un : Units → Float → Units
  un (noU x) = noU
  un (meter x) = meter
  un (gram x) = gram
  un (second x) = second 
  un (x u× y) = {!!} --cancel (un x 1.0 u× un y 1.0)
  un (x ^-1) = λ y → un x y ^-1
  -}

{-
  data operator : Set where
    `+ : operator
    `× : operator
-}
    
 -- _``+_ : Units → Units → Units
 -- _``+_ u1 u2 = {!!}
{-  
  data exp : Units → Set where
    V  : (y : Units) → exp y
    `+ : {x y : Units} → exp x → exp y → (un x) == (un y) → exp ((un x) (primFloatPlus (Val y) (Val x)))
    `- : {x y : Units} → exp x → exp y → (un x) == (un y) → exp ((un x) (primFloatMinus (Val y) (Val x)))
    `× : {x y : Units} → exp x → exp y → exp (x u× y)
    `÷ : {x y : Units} → exp x → exp y → exp (x u× (y ^-1))
-}
--  x : exp(meter(2.0))
--  x = `+ (V (meter (1.0))) (V(second(1.0))) Refl

--  x' : exp(meter(2.0))
--  x' = `+ (V (meter (1.0))) (V(meter(1.0))) Refl
