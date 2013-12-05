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

  infixl 10 _u×_
  
  infixl 11 _^-1
    
  data Imperial : Set where
    foot   : Imperial
    pound  : Imperial


  --need to remove noU if there are other units present
  listUtoU : List Units → Units
  listUtoU [] = noU
  listUtoU (x :: xs) = x u× listUtoU xs

  --need case for ^-1 ^-1 ?
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

  -- Bool represents whether a cancelation was made
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

--  test1 : makeFrac v == (meter :: noU :: [] , noU :: meter :: [])
--  test1 = Refl

  test2 : cancel (meter :: noU :: []) (noU :: meter :: []) == ([] , [])
  test2 = Refl

  test3 : listUtoU [] == noU

  test3 = Refl
  test4 : (listUtoU [] u× (listUtoU [] ^-1)) == (noU u× (noU ^-1))
  test4 = Refl
    
  testf : reduce v == noU
  testf = Refl 

  v' : Units
  v' = (meter u× second) u× ((second u× second) ^-1)

  testv' : (reduce v') == (meter u× (second ^-1))
  testv' = Refl

  testv : reduce v == noU
  testv = Refl

  prefixed : (v : Float) → (p : prefix) → Float
  prefixed = {!!}

  data UF : Units → Set where
    V    : (U : Units) → UF U
    _`+_ : {U : Units} → UF U → UF U → UF U
    _`-_ : {U : Units} → UF U → UF U → UF U
    _`×_ : {U1 U2 : Units} → UF U1 → UF U2 → UF (reduce (U1 u× U2))
    _`÷_ : {U1 U2 : Units} → UF U1 → UF U2 → UF (reduce (U1 u× U2 ^-1))

  infixl 8 _`×_

  infixl 8 _`÷_

  infixl 4 _`+_

  infixl 4 _`-_

  tm/s² : UF (meter u× ((second u× second) ^-1))
  tm/s² = V meter `÷ (V second `× V second)

  _uf×_ : {u1 u2 : Units} → Float × UF u1 → Float × UF u2 → Float × ((UF u1) `× (UF u2))
  _uf×_ = {!!}
  
  _uf+_ : {u : Units} → Float × UF u → Float × UF u → Float × UF u
  (v1 , uf1) uf+ (v2 , uf2) = v1 f+ v2 , uf1 `+ uf2

  _uf-_ : {u : Units} → Float × UF u → Float × UF u → Float × UF u
  (v1 , uf1) uf- (v2 , uf2) = v1 f− v2 , uf1 `- uf2

  displacement : Float → UF second → Float × (UF meter)
  displacement t uf = {!uf!}


  {-
  --compute as a function that takes a UF and creates correspond float ops
  compute : {u : Units} → UF u → (Float → Float → Float)
  compute {u} (V .u) = λ x y → x
  compute (uf1 `+ uf2) = _f+_
  compute (uf1 `- uf2) = _f−_
  compute (uf1 `× uf2) = _f×_
  compute (uf1 `÷ uf2) = _f÷_
-}
  
{-
  --tried created data type of float and UF again, doesn't really work
  data Exp : Set where
    _of_ : {u : Units} → Float → UF u → Exp
  _e+_ : Exp → Exp → Exp
  (v1 of u1) e+ (v2 of  u2) = {!(v1 f+ v2) of (u1 `+ u2)!} --can't enfor u1 == u2
  _e×_ : Exp → Exp → Exp
  (v1 of u1) e× (v2 of u2) = (v1 f× v2) of (u1 `× u2)
-}
--  g : UF (~ 9.8) (meter u× ((second u× second) ^-1))
--  g = V (primFloatMinus 0.0 9.8) (meter u× ((second u× second) ^-1))

--  displacement : Float → (UF second) → Float × (UF meter)
--  displacement t U = {!!} --`× (`× (`× (V 0.5 noU) g) t) t

  {-
  displacement : {t' : Float} → (UF t' second) → (UF (primFloatTimes (primFloatTimes (primFloatMinus 0.0 4.9) t') t') meter)
  displacement t = `× (`× (`× (V 0.5 noU) g) t) t

  x : UF (valUF (displacement (V 1.0 second))) (unitsUF (displacement (V 1.0 second)))
  x = displacement (V 1.0 second)
  +UF : {u : Units} → Float → Float → UF u → Float
  +UF v1 v2 uf = primFloatPlus v1 v2

  -UF : {u : Units} → Float → Float → UF u → Float
  -UF v1 v2 uf = primFloatMinus v1 v2

  --×UF : {u : Units} → Float → Float → UF u1 → UF u2 → F

 
  compute : {u1 u2 u3 : Units} → Float → Float → UF u1 → UF u2 → Float × (V u3)
  compute {u} v v2 (V .u) = {!!}
  compute v v2 (uf `+ uf₁) = {!compute !}
  compute v v2 (uf `- uf₁) = {!!}
  compute v v2 (uf `× uf₁) = {!!}
  compute v v2 (uf `÷ uf₁) = {!!}
-}
{-
  valUF : {x : Float} {U : Units} → UF U → Float
  valUF {x} {U} (V .U) = x
  valUF (`+ x1 x2) = primFloatPlus (valUF x1) (valUF x2)
  valUF (`- x1 x2) = primFloatMinus (valUF x1) (valUF x2)
  valUF (`× x1 x2) = primFloatTimes (valUF x1) (valUF x2)
  valUF (`÷ x1 x2) = primFloatDiv (valUF x1) (valUF x2)

  unitsUF : {x : Float} {U : Units} → UF x U → Units
  unitsUF {x} {U} (V .x .U) = U
  unitsUF (`+ x1 x2) = unitsUF x1
  unitsUF (`- x1 x2) = unitsUF x1
  unitsUF (`× x1 x2) = reduce ((unitsUF x1) u× (unitsUF x2))
  unitsUF (`÷ x1 x2) = reduce ((unitsUF x1) u× (unitsUF x2))


  data UFI : Set where
    _of_ : Float → Imperial → UFI

  data Metric : Set where
    _◂_ : prefix → Units → Metric   --\t
  
  data pUF : Set where
    _of_ : Float → Metric → pUF


  prefixed : {v : Float} {u : Units} (puf : pUF) → UF v u
  prefixed (v of (yotta ◂ u)) = V (primFloatTimes v 1.0e24) u
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


  V1 : UF 1.0 meter
  V1 = V 1.0 meter

  V2 : UF 2.0 meter
  V2 = `+ V1 V1

  V3 : UF 1.0 (meter u× meter)
  V3 = `× V1 V1

  g : UF (primFloatMinus 0.0 9.8) (meter u× ((second u× second) ^-1))
  g = V (primFloatMinus 0.0 9.8) (meter u× ((second u× second) ^-1))

  displacement : {t' : Float} → (UF t' second) → (UF (primFloatTimes (primFloatTimes (primFloatMinus 0.0 4.9) t') t') meter)
  displacement t = `× (`× (`× (V 0.5 noU) g) t) t

  x : UF (valUF (displacement (V 1.0 second))) (unitsUF (displacement (V 1.0 second)))
  x = displacement (V 1.0 second)

  vx : Float
  vx = valUF x

  testvx : vx == primFloatMinus 0.0 4.9
  testvx = Refl
  
  ux : Units
  ux = unitsUF x

  testux : ux == meter
  testux = Refl

  x1 : UF (primFloatMinus 0.0 4.9) meter
  x1 = displacement (V 1.0 second)
-}
