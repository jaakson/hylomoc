module HyLoMoC where

import Data.List
import Data.Map

-- type for models.

data Model a = Model { worlds :: [a],
                       rels :: [a -> [a]],
                       val :: Form -> [a],
                       assn :: Form -> a,
                       g :: Form -> a }



-- shorthand for Data.Map.lookup.
mlookup :: (Ord k) => k -> Map k a -> Maybe a
mlookup = Data.Map.lookup


-- turns a list into a function from fst to snd.

functioner :: (Ord a) => [(a,b)] -> b -> (a -> b) 
functioner ls defaultvalue = 
                   let listmap = (Data.Map.fromList ls) in
                       (\y -> case (mlookup y listmap) of
                               (Just xs) -> xs
                               Nothing  -> defaultvalue)

-- a test model:

smallmodel = Model [1,2,3] 
    [functioner [(1, [1,2]),(2,[2])] [], functioner [(2, [1,3]),(3,[2])] []]
    (functioner [(Prop 1, [1,2]),(Prop 2, [1,3])] [])
    (\y -> case (mlookup y (Data.Map.fromList [(Cons 1, 1),(Cons 2, 2),((Cons 3), 3)])) of
                     (Just x) -> x
                     Nothing -> error "Non total assignment!")     
    (functioner [(Var 1,2), (Var 2,2)] 1)



infmodel = Model [1..] -- works
    [(\y -> [(y+1)])] -- works
    (functioner [(Prop 1,(Data.List.filter odd [1..])),
                 (Prop 2,(Data.List.filter even [1..]))] [])
    (\y -> case y of
           (Cons x) -> x
           _        -> error "Not a cons-nominal." )
    (\y -> case y of
           (Var x) -> x
           _        -> error "Not a var-nominal." )
         

-- showing models -- 

instance (Show a) => Show (Model a) where
  show (Model worlds rels val assn g) = "worlds = " ++ show worlds ++
                                       " rels = " ++ show (Data.List.map (\u -> (Data.List.map (\w -> (w, u w)) worlds)) rels)

-- showing models relative to [Prop] and/or [Cons] with *printout*.

printout :: Show a => (Model a) -> [Form] -> [Form] -> String
printout m [] [] = "{ " ++ show m ++ " }"
printout m ps [] = "{ " ++ show m ++ ", val = " ++ show (Data.List.map
                                      (\x -> (x, val m x)) ps) ++ " }"
printout m [] ns = "{ " ++ show m ++ ", assn = " ++ show (Data.List.map
                                      (\x -> (x, assn m x)) ns) ++ " }"
printout m ps ns = "{ " ++ show m ++ ", val = " ++ show (Data.List.map
                                      (\x -> (x, val m x)) ps) ++ 
                                      ", assn = " ++ show (Data.List.map
                                      (\x -> (x, assn m x)) ns) ++ " }"



-- type for formulae.
type Name = Int
data Form = Prop Name
          | Cons Name 
          | Var Name        
          | Neg Form
          | Cnj Form Form
          | Dia Int Form
          | At Form Form
          | Exists Form
          | Binder Form Form
          deriving (Eq, Ord)


-- showing formulae.

instance Show Form where 
  show (Prop p)      = "p_" ++ show p
  show (Cons i)      = "i_" ++ show i
  show (Var x)       = "x_" ++ show x
  show (Neg f)       = '~' : show f 
  show (Cnj f1 f2)   = show f1 ++ " & " ++ show f2
  show (Dia n f)       = "<" ++ show n ++ ">" ++ show f
  show (At i f)      = "@_" ++ show i ++ " (" ++ show f ++ ")"
  show (Exists f)    = "E (" ++ show f ++ ")"
  show (Binder x f)  = "!_" ++ show x ++ " (" ++ show f ++ ")"
 
-- duals.

box :: Int -> Form -> Form
box n f = Neg (Dia n  (Neg f))

forAll :: Form -> Form
forAll f = Neg (Exists (Neg f))

-- Actual model checker, hyLoMoC.

hyLoMoC :: (Ord a) => Model a -> Form -> [a]
hyLoMoC m f = case (worlds m) of
                 [] -> error "This model is empty!"
                 xs -> Data.List.filter (\y -> isTruein m y f) (worlds m)

-- pointed model-checker.

isTruein :: (Ord a) => (Model a) -> a -> Form -> Bool
isTruein m w (Prop x)     = elem w (val m (Prop x))
isTruein m w (Cons x)     = assn m (Cons x) == w
isTruein m w (Var x)      = g m (Var x) == w
isTruein m w (Neg f)      = not (isTruein m w f)
isTruein m w (Cnj f1 f2)  = (isTruein m w f1) && (isTruein m w f2)
isTruein m w (Dia n f)      = any (\y -> isTruein m y f) (((rels m) !! n) w)
isTruein m w (At i f)     = isTruein m (assn m i) f
isTruein m w (Exists f)   = any ( \y -> isTruein m y f) (worlds m)
isTruein m w (Binder x f) = isTruein (Model (worlds m) 
                                      (rels m)
                                      (val m)
                                      (assn m)
                                      (\y -> case (x == y) of
                                         True  -> w
                                         False -> g m y)) w f

-- checks formulae to see if they are well-formed:

wff :: Form -> Bool
wff (Prop x)            = True
wff (Cons x)            = True
wff (Var x)             = True
wff (Neg f)             = wff f
wff (Cnj f1 f2)         = wff f1 && wff f2
wff (Dia n f)           = wff f
wff (At (Cons x) f)     = wff f
wff (At (Var x) f)      = wff f
wff (At x f)            = False
wff (Exists f)          = wff f
wff (Binder (Var x) f)  = wff f
wff (Binder x f)        = False
