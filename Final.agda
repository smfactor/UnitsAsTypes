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

--  open Nat using (_+_)
  open List using (_++_ ; [_] ; ++-assoc)
  
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
 

  funct : Float → Float
  funct x = cosine x f− x

  derivative : Float → Float → Float
  derivative x h = ((funct (x f+ h) f− funct (x f− h)) f÷ (2.0 f× h))
 
  ε : Float
  ε = 0.0000001
  p0 : Float
  p0 = π f÷ 4.0
  N : Float
  N = 3.0
  tol : Float 
  tol = 0.001

  --approximation algorithm for square roots of floats
  -- x : the number to take the square root of t ≥ 0
  -- ε : the relative error tolerance
  -- t : initial guess of root
  newtonian : Float → Float → Float → Float
  newtonian x ε t with primFloatLess (ε f× t) (abs (t f− (x f÷ t)))
  newtonian x ε t | True = newtonian x ε (((x f÷ t) f+ t) f÷ 2.0)
  newtonian x ε t | False = t

  sqrt : Float → Float
  sqrt x = newtonian x ε 2.0 
  

    
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

  infixl 10 _u×_
  infixl 11 _^-1    

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
  checkEqual x ((y ^-1) ^-1) = checkEqual x y
  checkEqual ((x ^-1) ^-1) y = checkEqual x y
  checkEqual x y = False


  cancelS : Units → List Units → (Bool × List Units)
  cancelS x [] = False , []
  cancelS x (y :: ys) with checkEqual x y
  cancelS x (y :: ys) | True = True , ys
  cancelS x (y :: ys) | False with cancelS x  ys
  cancelS x (y :: ys) | False | True , ys' = True , y :: ys'
  cancelS x (y :: ys) | False | False , ys' = False , y :: ys'


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
  makeFrac x = x :: [] , []

  filternoU : Units → Units
  filternoU (x u× noU) = filternoU x
  filternoU (noU u× x) = filternoU x
  filternoU (x u× x1) = filternoU x u× filternoU x1
  filternoU (x ^-1) = filternoU x ^-1
  filternoU x = x

  reduce : Units → Units 
  reduce x with makeFrac x
  reduce x | t , b with cancel t b
  reduce x | t , b | t' , [] = filternoU (listUtoU t')
  reduce x | t , b | t' , b' = filternoU (listUtoU t' u× (listUtoU b' ^-1))

  v : Units
  v = (meter u× (meter ^-1))
    
  v' : Units
  v' = (meter u× second) u× ((second u× second) ^-1)

  testv' : (reduce v') == (meter u× (second ^-1))
  testv' = Refl

  testv : reduce v == noU
  testv = Refl

  countUnits : List Units → List (Units × Nat)
  countUnits x = {!!}

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

  rt : Units → Units
  rt x with makeFrac x
  rt x | t , b with countUnits t | countUnits b
  rt x | t , b | ts | bs with Uroot ts | Uroot bs
  rt x | t , b | ts | bs | Some rt | Some rb = filternoU (listUtoU rt u× listUtoU rb ^-1)
  rt x | t , b | ts | bs | Some rt | None = {!!}
  rt x | t , b | ts | bs | None | Some rb = {!!}
  rt x | t , b | ts | bs | None | None = {!!}

  data UF : Units → Set where
    V    : (f : Float) → (U : Units) → UF U
    P    : (f : Float) → (p : Prefix) → (U : Units) → UF U
    _`+_ : {U : Units} → UF U → UF U → UF U
    _`-_ : {U : Units} → UF U → UF U → UF U
    _`×_ : {U1 U2 : Units} → UF U1 → UF U2 → UF (reduce (U1 u× U2))
    _`÷_ : {U1 U2 : Units} → UF U1 → UF U2 → UF (reduce (U1 u× U2 ^-1))

  infixl 8 _`×_
  infixl 8 _`÷_
  infixl 4 _`+_
  infixl 4 _`-_

  g : UF (meter u× ((second u× second) ^-1))
  g = V (~ 9.8) (meter u× (second u× second) ^-1)

  displacement : UF second → UF meter
  displacement t = V 0.5 noU `× g `× t `× t



--  x : Float
--  x = compute displacement 6.0
  
  --use UF to make dsl with rules ... plop down float and float is in units
  --function construct UF expression then compute it
  

  
  compute : {u : Units} → UF u → Float
  compute {u} (V f .u) = f
  compute {u} (P f p .u) = prefixed f p
  compute (x `+ x₁) = compute x f+ compute x₁
  compute (x `- x₁) = compute x f− compute x₁
  compute (x `× x₁) = compute x f× compute x₁
  compute (x `÷ x₁) = compute x f÷ compute x₁



  tm/s² : UF (meter u× ((second u× second) ^-1))
  tm/s² = V (~ 4.9) meter `÷ (V 1.0 second `× V 1.0 second)




  mm : UF meter
  mm = V 1.0 meter
  ss : UF second
  ss = V 1.0 second









--if doing
  --dont leav unitland
  --whole program is of type UF 
  --runtimes system actually runs compuation

    --give anything that compute uf second and will compute uf meter

  dis1sec : Float
  dis1sec = compute (displacement (V 1.0 second))






{-
  data UF' : Float → Units → Set where
    `V    : (v : Float) → (U : Units) → UF' v U
    _``+_ : {x y : Float} {U : Units} → UF' x U → UF' y U → UF' (x f+ y) U
    _``-_ : {x y : Float} {U : Units} → UF' x U → UF' y U → UF' (x f− y) U
    _``×_ : {x y : Float} {U1 U2 : Units} → UF' x U1 → UF' y U2 → UF' (x f× y) (reduce (U1 u× U2))
    _``÷_ : {x y : Float} {U1 U2 : Units} → UF' x U1 → UF' y U2 → UF' (x f÷ y) (reduce (U1 u× U2 ^-1))

  valUF' : {x : Float} {U : Units} → UF' x U → Float
  valUF' {x} {U} (`V .x .U) = x
  valUF' (x1 ``+ x2) = primFloatPlus (valUF' x1) (valUF' x2)
  valUF' (x1 ``- x2) = primFloatMinus (valUF' x1) (valUF' x2)
  valUF' (x1 ``× x2) = primFloatTimes (valUF' x1) (valUF' x2)
  valUF' (x1 ``÷ x2) = primFloatDiv (valUF' x1) (valUF' x2)

  unitsUF' : {x : Float} {U : Units} → UF' x U → Units
  unitsUF' {x} {U} (`V .x .U) = U
  unitsUF' (x1 ``+ x2) = unitsUF' x1
  unitsUF' (x1 ``- x2) = unitsUF' x1
  unitsUF' (x1 ``× x2) = reduce ((unitsUF' x1) u× (unitsUF' x2))
  unitsUF' (x1 ``÷ x2) = reduce ((unitsUF' x1) u× (unitsUF' x2))

  g : UF' (primFloatMinus 0.0 9.8) (meter u× ((second u× second) ^-1))
  g = `V (primFloatMinus 0.0 9.8) (meter u× ((second u× second) ^-1))

  displacement : {t' : Float} → (UF' t' second) → (UF' (primFloatTimes (primFloatTimes (primFloatMinus 0.0 4.9) t') t') meter)
  displacement t = (((`V 0.5 noU) ``× g) ``× t) ``× t

  x : UF' (valUF' (displacement (`V 1.0 second))) (unitsUF' (displacement (`V 1.0 second)))
  x = displacement (`V 1.0 second)
-}
{-
module ReduceUnits' where
  Units' : Set
  C : Units → Units
  cancel : {u : Units} u u× u ^-1 == noU



  data Reduced : Set where
    UTrans  : ?
    URefl   : ?
    USim    : ?
    UCong   : ?
    UnoU-1  : (noU ^-1) == noU
-- more cases here if u is not next to u^-1?
    Ucancel1 : {u : Units} u u× (u ^-1) == noU
    Ucancel2 : {u : Units} (u ^-1) u× u == noU
    Uid1     : {u : Units} u u× noU == u
    Uid2     : {u : Units} noU u× u == u

-}
