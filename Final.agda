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
    _*_ : Float → Units → UF

  test : UF
  test = 1.0 * noU

  listUtoU : List Units → Units
  listUtoU [] = {!noU!}
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


  --cancel should remove all tuplicates in the two lists
  cancel : (List Units × List Units) → (List Units × List Units)
  cancel ([] , []) = ([] , [])
  cancel ([] , bs) = ([] , bs)
  cancel (ts , []) = (ts , [])
  cancel (t :: ts , b :: bs) with checkEqual t b 
  cancel (t :: ts , b :: bs) | True = cancel (ts , bs)
  cancel (t :: ts , b :: bs) | False with cancel (t :: ts , bs)
  cancel (t :: ts , b :: bs) | False | t1 , b1 with cancel (t1 , b :: b1)
  cancel (t :: ts , b :: bs) | False | t1 , b1 | t2 , b2 = {!t2!} , {!b2!}

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
  reduce x with cancel (makeFrac x)
  reduce x | t , b = listUtoU t u× (listUtoU b ^-1)

   
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
