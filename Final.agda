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
    primSin          : Float → Float
    primFloatLess    : Float → Float → Bool

  open List using (_++_ ; [_] ; ++-assoc)
  
  {- Some definitions for floating point operations -}
  _f+_ : Float → Float → Float
  x f+ y = primFloatPlus x y
 
  _f−_ : Float → Float → Float --\minus
  x f− y = primFloatMinus x y

  _f×_ : Float → Float → Float --\times
  x f× y = primFloatTimes x y

  _f÷_ : Float → Float → Float --\div
  x f÷ y = primFloatDiv x y
 
  ~_ : Float → Float
  ~ x = primFloatMinus 0.0 x

  infix 10 ~_

  abs : Float → Float
  abs x with primFloatLess x 0.0 
  abs x | True = ~ x
  abs x | False = x
  
  π : Float
  π = 3.1415926

  cosine : Float → Float
  cosine θ = primSin ((π f÷ 2.0) f− θ)
 
  --approximation algorithm for square roots of floats
  -- x : the number to take the square root of t ≥ 0
  -- ε : the relative error tolerance
  -- t : initial guess of root
  newtonian : Float → Float → Float → Float
  newtonian x ε t with primFloatLess (ε f× t) (abs (t f− (x f÷ t)))
  newtonian x ε t | True = newtonian x ε (((x f÷ t) f+ t) f÷ 2.0)
  newtonian x ε t | False = t

  √ : Float → Float
  √ x = newtonian x 0.0000001 2.0
  
  {- datatype for SI units -}  
  data Units : Set where
    noU     : Units    --units for not units
    meter   : Units
    gram    : Units
    second  : Units
    ampere  : Units
    kelvin  : Units
    candela : Units
    mol     : Units
    _u×_    : Units → Units → Units     --multiplication of two units
    _^-1    : Units → Units             -- inversion of a unit

  infixl 10 _u×_
  infixl 11 _^-1    
                                                                                         
  {- datatype for prefixes to SI units -}
  data Prefix : Set where
    yotta : Prefix
    zetta : Prefix
    exa   : Prefix
    peta  : Prefix
    tera  : Prefix
    giga  : Prefix
    mega  : Prefix
    kilo  : Prefix
    hecto : Prefix
    deca  : Prefix
    deci  : Prefix 
    centi : Prefix
    milli : Prefix
    micro : Prefix
    nano  : Prefix
    pico  : Prefix
    femto : Prefix
    atto  : Prefix
    zepto : Prefix
    yocto : Prefix

  {- Converts a prefixed float to a float of a base unit -}
  prefixed : Float → Prefix → Float
  prefixed f yotta = f f× 1.0e24
  prefixed f zetta = f f× 1.0e21
  prefixed f exa = f f× 1.0e18
  prefixed f peta = f f× 1.0e15
  prefixed f tera = f f× 1.0e12
  prefixed f giga = f f× 1.0e9
  prefixed f mega = f f× 1000000.0
  prefixed f kilo = f f× 1000.0
  prefixed f hecto = f f× 100.0
  prefixed f deca = f f× 10.0
  prefixed f deci = f f÷ 10.0
  prefixed f centi = f f÷ 100.0
  prefixed f milli = f f÷ 1000.0
  prefixed f micro = f f÷ 1000000.0
  prefixed f nano = f f÷ 1.0e9
  prefixed f pico = f f÷ 1.0e12
  prefixed f femto = f f÷ 1.0e15
  prefixed f atto = f f÷ 1.0e18
  prefixed f zepto = f f÷ 1.0e21
  prefixed f yocto = f f÷ 1.0e24


  {- Helper functions for reduce -}

  {- converts a list of units into a single unit -}
  listUtoU : List Units → Units
  listUtoU [] = noU
  listUtoU (x :: xs) = x u× listUtoU xs

  {- checks if two units are equal -}
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
  checkEqual x ((y ^-1) ^-1) = checkEqual x y
  checkEqual ((x ^-1) ^-1) y = checkEqual x y
  checkEqual x y = False

  
  cancelS : Units → List Units → (Bool × List Units)
  cancelS x [] = False , []
  cancelS noU ys = True , ys
  cancelS x (noU :: ys) = cancelS x ys
  cancelS x (y :: ys) with checkEqual x y
  cancelS x (y :: ys) | True = True , ys
  cancelS x (y :: ys) | False with cancelS x  ys
  cancelS x (y :: ys) | False | True , ys' = True , y :: ys'
  cancelS x (y :: ys) | False | False , ys' = False , y :: ys'

  {- Takes a list of the units on top and a list of the units on bottom and cancels
     them to produce of a tuple of a list of top units and a list of bottom units -}
  cancel : List Units → List Units → (List Units × List Units)
  cancel [] b = [] , b
  cancel (x :: ts) b with cancelS x b
  cancel (x :: ts) b | True , b' = cancel ts b'
  cancel (x :: ts) b | False , _ with cancel ts b
  cancel (x :: ts) b | False , _ | t' , b' = x :: t' , b'

  {- Takes a units and returns a list of top units and a list of bottom units -}
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
  makeFrac x = x :: [] , []
  
  {- removes all noU from a units -}
  filternoU : Units → Units
  filternoU (x u× noU) = filternoU x
  filternoU (noU u× x) = filternoU x
  filternoU (x u× (noU ^-1)) = filternoU x
  filternoU ((noU ^-1) u× x) = filternoU x
  filternoU (x u× x1) with filternoU x | filternoU x1
  ... | noU | noU = noU
  ... | u | noU = u
  ... | noU | u = u
  ... | u1 | u2 = u1 u× u2
  filternoU (x ^-1) = filternoU x ^-1
  filternoU x = x

  {- reduces a unit -}
  reduce : Units → Units 
  reduce x with makeFrac x
  reduce x | t , b with cancel t b
  reduce x | t , b | t' , [] = filternoU (listUtoU t')
  reduce x | t , b | t' , b' = filternoU (listUtoU t' u× (listUtoU b' ^-1))

 
  {- Makes square of root units, assumes unit is square-root-able -}
  addUnits : Units → List (Units × Nat) → List (Units × Nat)
  addUnits x [] = (x , 1) :: []
  addUnits x ((u , n) :: ys) with checkEqual x u
  addUnits x ((u , n) :: ys) | True = (u , S n) :: ys
  addUnits x ((u , n) :: ys) | False = (u , n) :: addUnits x ys

  --helper for counting number of each units in list
  countUnits' : List Units  → List (Units × Nat) → List (Units × Nat)
  countUnits' [] r = r
  countUnits' (x :: xs) r = countUnits' xs (addUnits x r)

  countUnits : List Units → List (Units × Nat)
  countUnits ls = countUnits' ls []

  makeRoot : Units × Nat → Maybe (List Units)
  makeRoot (U , Z) = Some []
  makeRoot (U , S Z) = None
  makeRoot (U , S (S n)) with makeRoot (U , n)
  makeRoot (U , S (S n)) | Some x = Some (U :: x)
  makeRoot (U , S (S n)) | None = None

  Uroot : List (Units × Nat) → Maybe (List Units)
  Uroot [] = Some []
  Uroot ((U , Z) :: xs) = Uroot xs
  Uroot (x :: xs) with makeRoot x 
  Uroot (x :: xs) | None = None
  Uroot (x :: xs) | Some y with Uroot xs
  Uroot (x :: xs) | Some y | Some z = Some (y ++ z)
  Uroot (x :: xs) | Some y | None = None
  {- Find the Units of the square root of a unit -}
  rt : Units → Maybe Units
  rt x with makeFrac x
  rt x | t , b with countUnits t | countUnits b
  rt x | t , b | ts | bs with Uroot ts | Uroot bs
  rt x | t , b | ts | bs | Some rt | Some rb = Some (filternoU (listUtoU rt u× listUtoU rb ^-1))
  rt x | t , b | ts | bs | Some rt | None = {!!}
  rt x | t , b | ts | bs | None | Some rb = {!!}
  rt x | t , b | ts | bs | None | None = {!!}


  {- Inductive family indexed by unit representing units are 'correct', ie
     the units are in reduced form and -}
  data UF : Units → Set where
    V    : (f : Float) → (U : Units) → UF U
    P    : (f : Float) → (p : Prefix) → (U : Units) → UF U
    _`+_ : {U : Units} → UF U → UF U → UF U
    _`-_ : {U : Units} → UF U → UF U → UF U
    _`×_ : {U1 U2 : Units} → UF U1 → UF U2 → UF (reduce (U1 u× U2))
    _`÷_ : {U1 U2 : Units} → UF U1 → UF U2 → UF (reduce (U1 u× U2 ^-1))
--    `√_  : {U : Units} → UF (U u× U) → UF U

  infixl 8 _`×_
  infixl 8 _`÷_
  infixl 4 _`+_
  infixl 4 _`-_

  {- Calculate the floating point value held in a unit -}
  compute : {u : Units} → UF u → Float
  compute {u} (V f .u) = f
  compute {u} (P f p .u) = prefixed f p
  compute (x `+ x₁) = compute x f+ compute x₁
  compute (x `- x₁) = compute x f− compute x₁
  compute (x `× x₁) = compute x f× compute x₁
  compute (x `÷ x₁) = compute x f÷ compute x₁
--  compute (`√ x) = √ (compute x)

  {- Helper function to count the number of each base unit in a unit -}
  count' : Units → Bool → (Float × Float × Float × Float × Float × Float × Float) → (Float × Float × Float × Float × Float × Float × Float)
  count' noU True (m , g , s , a , k , c , mo) = m , g , s , a , k , c , mo
  count' meter True (m , g , s , a , k , c , mo) = m f+ 1.0 , g , s , a , k , c , mo
  count' gram True (m , g , s , a , k , c , mo) = m , g f+ 1.0 , s , a , k , c , mo
  count' second True (m , g , s , a , k , c , mo) = m , g , s f+ 1.0 , a , k , c , mo
  count' ampere True (m , g , s , a , k , c , mo) = m , g , s , a f+ 1.0 , k , c , mo
  count' kelvin True (m , g , s , a , k , c , mo) = m , g , s , a , k f+ 1.0 , c , mo
  count' candela True (m , g , s , a , k , c , mo) = m , g , s , a , k , c f+ 1.0 , mo
  count' mol True (m , g , s , a , k , c , mo) = m , g , s , a , k , c , mo f+ 1.0
  count' noU False (m , g , s , a , k , c , mo) = m , g , s , a , k , c , mo
  count' meter False (m , g , s , a , k , c , mo) = m f− 1.0 , g , s , a , k , c , mo
  count' gram False (m , g , s , a , k , c , mo) = m , g f− 1.0 , s , a , k , c , mo
  count' second False (m , g , s , a , k , c , mo) = m , g , s f− 1.0 , a , k , c , mo
  count' ampere False (m , g , s , a , k , c , mo) = m , g , s , a f− 1.0 , k , c , mo
  count' kelvin False (m , g , s , a , k , c , mo) = m , g , s , a , k f− 1.0 , c , mo
  count' candela False (m , g , s , a , k , c , mo) = m , g , s , a , k , c f− 1.0 , mo
  count' mol False (m , g , s , a , k , c , mo) = m , g , s , a , k , c , mo f− 1.0
  count' (u u× u1) flag xs with count' u flag xs
  ... | xs' = count' u1 flag xs'
  count' (u ^-1) True xs = count' u False xs
  count' (u ^-1) False xs = count' u True xs

  {- counts the number of each base unit in a unit -}
  count : Units → Float × Float × Float × Float × Float × Float × Float
  count u = count' u True (0.0 , 0.0 , 0.0 , 0.0 , 0.0 , 0.0 , 0.0)

  {- Inductive family representing when two units are equivalent. -}
  data Equivalent : Units → Units → Set where
    Equiv : (u1 : Units) → (u2 : Units) → count (reduce u1) == count (reduce u2) → Equivalent u1 u2

  {- Proof that for all units, reduce of those units are equivalent to those units -}
  reduceEquiv : (u : Units) → Equivalent u (reduce u)
  reduceEquiv noU = Equiv noU noU Refl
  reduceEquiv meter = Equiv meter meter Refl
  reduceEquiv gram = Equiv gram gram Refl
  reduceEquiv second = Equiv second second Refl
  reduceEquiv ampere = Equiv ampere ampere Refl
  reduceEquiv kelvin = Equiv kelvin kelvin Refl
  reduceEquiv candela = Equiv candela candela Refl
  reduceEquiv mol = Equiv mol mol Refl
  reduceEquiv (u u× u1) with cancel (fst (makeFrac (u u× u1))) (snd (makeFrac (u u× u1)))
  reduceEquiv (u u× u1) | [] , [] = {!!}
  reduceEquiv (u u× u1) | [] , b :: bs = {!!}
  reduceEquiv (u u× u1) | t :: ts , [] = {!!}
  reduceEquiv (u u× u1) | t :: ts , b :: bs with filternoU (t u× listUtoU ts) | filternoU (b u× listUtoU bs) ^-1
  ... | P1 | P2 = {!!}
  reduceEquiv (u ^-1) with cancel (fst (makeFrac (u ^-1))) (snd (makeFrac (u ^-1)))
  reduceEquiv (u ^-1) | [] , [] = {!!}
  reduceEquiv (u ^-1) | [] , b :: bs = {!!}
  reduceEquiv (u ^-1) | t :: ts , [] = {!!}
  reduceEquiv (u ^-1) | t :: ts , b :: bs with filternoU (t u× listUtoU ts) | filternoU (b u× listUtoU bs) ^-1
  ... | P1 | P2 = {!!}

  {- Proof that reduce x is in reduced form, ie it cannot be reduced any further -}
  reduced-X : (u : Units) → reduce u == reduce (reduce u)
  reduced-X u = {!!}
  
  -- tests for reduce 
  v : Units
  v = (meter u× (meter ^-1))
    
  v' : Units
  v' = (meter u× second) u× ((second u× second) ^-1)

  v1 : Units
  v1 = meter u× second ^-1

  v2 : Units
  v2 = (meter u× second ^-1) u× noU

  v3 : List Units × List Units
  v3 = makeFrac v2

  testv' : (reduce v') == (meter u× (second ^-1))
  testv' = Refl

  testv : reduce v == noU
  testv = Refl

  -- tests for compute 
  g : UF (meter u× ((second u× second) ^-1))
  g = V (~ 9.8) (meter u× (second u× second) ^-1)

  displacement : UF second → UF meter
  displacement t = V 0.5 noU `× g `× t `× t

  tm/s² : UF (meter u× ((second u× second) ^-1))
  tm/s² = V (~ 4.9) meter `÷ (V 1.0 second `× V 1.0 second)

  computetest : Float
  computetest = compute (displacement (V 1.0 second))

  dis1sec : Float
  dis1sec = compute (displacement (V 1.0 second))

   -- tests of operations using UF
  treduce :  Units
  treduce = reduce (noU u× (meter u× (second u× second) ^-1))

  vtest : UF (meter u× second ^-1)
  vtest = V 1.0 meter `÷ V 1.0 second
  v2test : UF (meter u× meter u× (second u× second) ^-1)
  v2test = vtest `× vtest
  gytest : UF (meter u× meter u× (second u× second) ^-1)
  gytest = V 2.0 noU `× V (~ 9.8) (meter u× (second u× second) ^-1) `×
               V 1.0 meter
  v2gy : UF (meter u× meter u× (second u× second) ^-1)
  v2gy = v2test `+ gytest

  sqrt-test : (UF (meter u× second ^-1))
  sqrt-test = {!`√ v2gy!}

 {- Library for example of code -}
  module Projectile where
    cos : UF noU → UF noU
    cos θ = V (primSin (primFloatMinus (primFloatDiv π 2.0) (compute θ))) noU
    sin : UF noU → UF noU
    sin θ = V (primSin (compute θ)) noU
--    sqrt : {u : Units} → UF u → UF u
--    sqrt = {!!}

    {- calculates the horizontal distance traveled by a projectile fired from ground height -}
    h-dist-trav : UF (meter u× (second ^-1))   --velocity
                  → UF noU                               --angle
                  → UF (meter u× ((second u× second) ^-1)) -- gravitational constant
                  → UF meter                                -- distance traveled
    h-dist-trav v θ g = v `× cos θ `÷ g `× (V 2.0 noU `× (v `× sin θ))

    {- Calculates the maximum vertical height of a projectile -}
    max-height : UF (meter u× (second ^-1))   --velocity
                → UF noU                               --angle
                → UF meter                             -- initial height
                → UF (meter u× ((second u× second) ^-1)) -- gravitational constant
                → UF meter                                -- maximum height
    max-height v θ y₀ g = ((v `× v `× sin θ `× sin θ) `÷ ((V (~ 2.0) noU) `× g))

 
