module AST where
import qualified Control.Monad as M
import qualified Data.List as L

type Error = String
data Loc = 
  Loc { locix :: Int, locline :: Int, loccol :: Int } deriving(Eq)

instance Show Loc where
  show (Loc ix line col) = "Loc(" ++ show line ++ ":" ++ show col ++ " " ++ show ix ++ ")"

errAtLoc :: Loc -> String  -> String
errAtLoc (Loc _ line col) err =
  show line ++ ":" ++ show col ++ " " ++ err

data Span = Span { spanl :: Loc, spanr :: Loc } deriving(Eq)

instance Show Span where
  show (Span l r) = "Span(" ++ show l ++ " " ++ show r ++ ")"

errAtSpan :: Span -> String -> String
errAtSpan (Span (Loc _ lline lcol) (Loc _ rline rcol)) err = 
    show lline  ++ ":" ++ show lcol ++ " - " ++ 
    show rline ++ ":" ++ show rcol ++ " " ++
    err

data Delimiter = Round | Square | Flower deriving(Eq, Show)

data Token = Open Span Delimiter | Close Span Delimiter | Str Span String deriving(Show)

-- The Char of a tuple carries what the open bracket looks like.
data AST = 
    Tuple { 
      astspan :: Span,
      tupledelimiter :: Delimiter,
      tupleget :: [AST]
    } | 
    Atom { 
      astspan :: Span,
      atomget :: String
    } deriving (Show)

delimOpen :: Delimiter -> String
delimOpen Round = "("
delimOpen Square = "["
delimOpen Flower = "{"

delimClose Round = ")"
delimClose Square = "]"
delimClose Flower = "}"


astPretty :: AST -> String
astPretty (Atom _ l) = l
astPretty (Tuple _ delim ls) = 
  delimOpen delim ++ L.intercalate " " (map astPretty ls) ++ delimClose delim

astSpan :: AST-> Span
astSpan (Tuple span _ _) = span
astSpan (Atom span _) = span

spanExtend :: Span -> Span -> Span
spanExtend (Span l r) (Span l' r') = Span l r'


locNextCol :: Loc -> Loc
locNextCol (Loc ix line col) = Loc (ix+1) line (col+1)

locNextCols :: Int -> Loc -> Loc
locNextCols n (Loc ix line col) = Loc (ix+n) line (col+n)

locNextLine :: Loc -> Loc
locNextLine (Loc ix line col) = Loc (ix+1) (line+1) 1

isSigil :: Char -> Bool
isSigil '(' = True
isSigil ')' = True
isSigil '[' = True
isSigil ']' = True
isSigil '{' = True
isSigil '}' = True
isSigil ' ' = True
isSigil '\n' = True
isSigil '\t' = True
isSigil _ = False

tokenize :: Loc -> String -> [Token]
tokenize l [] = []
tokenize l ('\n':cs) = tokenize (locNextLine l) cs
tokenize l ('\t':cs) = tokenize (locNextCol l) cs
tokenize l (' ':cs) = tokenize (locNextCol l) cs

tokenize l ('(':cs) = 
    let l' =  locNextCol l; span = Span l l'
    in (Open span Round):tokenize l' cs
tokenize l (')':cs) = 
    let l' = locNextCol l; span = Span l l'
    in (Close span Round):tokenize l' cs

tokenize l ('[':cs) = 
    let l' =  locNextCol l; span = Span l l'
    in (Open span Square):tokenize l' cs
tokenize l (']':cs) = 
    let l' = locNextCol l; span = Span l l'
    in (Close span Square):tokenize l' cs

tokenize l ('{':cs) = 
    let l' =  locNextCol l; span = Span l l'
    in (Open span Flower):tokenize l' cs
tokenize l ('}':cs) = 
    let l' = locNextCol l; span = Span l l'
    in (Close span Flower):tokenize l' cs


tokenize l cs = 
    let (lex, cs') = L.span (not . isSigil) cs
        l' = locNextCols (length lex) l
        span = Span l l'
    in (Str span lex):tokenize l' cs'

tupleAppend :: AST -> AST -> AST
tupleAppend (Atom _ _) s = error $ "cannot push into atom"
tupleAppend (Tuple span delim ss) s = Tuple (spanExtend span (astSpan s)) delim (ss ++ [s])

-- | invariant: stack, top only contain `Tuple`s.
doparse :: [Token] -- ^ stream of tokens
  -> AST -- ^ currently building AST
  ->  [AST] -- ^ stack of AST 
  -> Either Error AST  -- final AST
doparse [] cur [] = Right cur
doparse [] cur (top:stack') =
  Left $ errAtLoc (spanl (astSpan top)) "unclosed open bracket."
doparse ((Open span delim):ts) cur stack = 
  doparse ts (Tuple span delim [])  (cur:stack) -- open new tuple
doparse ((Close span delim):ts) cur stack = 
  if tupledelimiter cur == delim -- we close the current thing correctly
  then case stack of  -- pop stack, and append cur into top, make top cur
            (top:stack') -> doparse ts (tupleAppend top cur) stack'
            [] -> Left $ errAtSpan span "too many close parens." 
  else Left $ errAtLoc (spanl . astspan $ cur) "mismatched bracket (open) " ++ 
              "'" ++ (delimOpen (tupledelimiter cur)) ++ "'" ++ 
              "; " ++ 
              errAtLoc (spanl span) "mismatched bracket (close) " ++
              "'" ++ (delimClose delim) ++ "'"

doparse ((Str span str):ts) cur stack = 
  doparse ts (tupleAppend cur (Atom span str)) stack -- append into tuple

-- | parse a string
parse :: String -> Either Error AST
parse s =
  let locBegin = Loc 0 1 1
      spanBegin = Span locBegin locBegin
  in doparse (tokenize locBegin s) (Tuple spanBegin Flower []) []



at :: Int -> AST -> Either Error AST
at ix (Atom span _) = 
 Left $ errAtSpan span $ 
   "expected tuple index " ++ show ix ++
   ". Found atom. "
at ix (Tuple span _ xs) = 
  if length xs < ix
  then Left $ errAtSpan span $ 
    "expected tuple index " ++ show ix ++ 
    ". Found tuple of smaller length: "  ++ show (length xs)
  else return (xs !! ix)

atomString :: String -> AST -> Either Error ()
atomString str (Atom span s) = 
  if str == s
  then return ()
  else Left $ errAtSpan span $ 
    "expected atom '" ++ str ++ ". Found atom '" ++ s ++ "'"
atomString str (Tuple span _ _) =
  Left $ errAtSpan span $ 
    "expected atom '" ++ str ++ "'. Found tuple."

atom :: AST -> Either Error String
atom t@(Tuple span _ xs) = 
  Left $ errAtSpan span $
    "expected atom, found tuple.\n" ++ astPretty t
atom (Atom span a) = return a

tuple :: Int -> AST -> Either Error [AST]
tuple n (Atom span atom) = 
  Left $ errAtSpan span $ "expected tuple of length " ++ show n ++ 
         ". found atom " ++ show atom
tuple n ast@(Tuple span _ xs) = 
 if length xs /= n 
 then Left $ errAtSpan span $ 
    "expected tuple of length " ++ show n ++
    ". found tuple of length " ++ show (length xs)  ++ 
    " |" ++ astPretty ast ++ "|."
 else Right xs

tuple4 :: AST -> Either Error (AST, AST, AST, AST)
tuple4 ast = do
    xs <- tuple 4 ast
    return (xs !! 0, xs !! 1, xs !! 2, xs !! 3)

-- | functional version of tuple 2
tuple2f :: (AST -> Either Error a0) 
    -> (AST -> Either Error a1) 
    -> AST -> Either Error (a0, a1)
tuple2f f0 f1 ast = do
    xs <- tuple 2 ast
    a0 <- f0 (xs !! 0)
    a1 <- f1 (xs !! 1)
    return (a0, a1)

-- | functional version of tuple 3
tuple3f :: (AST -> Either Error a0) 
    -> (AST -> Either Error a1) 
    -> (AST -> Either Error a2) 
    -> AST -> Either Error (a0, a1, a2)
tuple3f f0 f1 f2 ast = do
    xs <- tuple 3 ast
    a0 <- f0 (xs !! 0)
    a1 <- f1 (xs !! 1)
    a2 <- f2 (xs !! 2)
    return (a0, a1, a2)

-- | functional version of tuple 4
tuple4f :: (AST -> Either Error a0) 
    -> (AST -> Either Error a1) 
    -> (AST -> Either Error a2) 
    -> (AST -> Either Error a3) 
    -> AST -> Either Error (a0, a1, a2, a3)
tuple4f f0 f1 f2 f3 ast = do
    xs <- tuple 4 ast
    a0 <- f0 (xs !! 0)
    a1 <- f1 (xs !! 1)
    a2 <- f2 (xs !! 2)
    a3 <- f3 (xs !! 3)
    return (a0, a1, a2, a3)

tuple5f :: (AST -> Either Error a0) 
    -> (AST -> Either Error a1) 
    -> (AST -> Either Error a2) 
    -> (AST -> Either Error a3) 
    -> (AST -> Either Error a4) 
    -> AST -> Either Error (a0, a1, a2, a3, a4)
tuple5f f0 f1 f2 f3 f4 ast = do
    xs <- tuple 5 ast
    a0 <- f0 (xs !! 0)
    a1 <- f1 (xs !! 1)
    a2 <- f2 (xs !! 2)
    a3 <- f3 (xs !! 3)
    a4 <- f4 (xs !! 4)
    return (a0, a1, a2, a3, a4)

astignore :: AST -> Either Error ()
astignore _ = return ()

aststr :: String -> AST -> Either Error ()
aststr s (Atom span x) = 
    case s == x of
      True -> return ()
      False -> Left $ errAtSpan span $ 
        "expected string |" ++ s ++ "|. found |" ++ x ++ "|"

-- | create a list of tuple values
tuplefor :: (AST -> Either Error a) -> AST -> Either Error [a]
tuplefor f (Atom span _) =
  Left $ errAtSpan span $ 
    "expected tuple, found atom."
tuplefor f (Tuple span _ xs) = M.forM xs f 


tuplefor' :: (AST -> Either Error [a]) -> AST -> Either Error [a]
tuplefor' f (Atom span _) =
  Left $ errAtSpan span $ 
    "expected tuple, found atom."
tuplefor' f (Tuple span _ xs) = 
    case M.forM xs f of
        Left err -> Left err
        Right xss -> pure $ M.join xss

atomOneOf :: [String] -> AST -> Either Error String
atomOneOf _ (Tuple span _ xs) = 
  Left $ errAtSpan span $
    "expected atom, found tuple."
atomOneOf expected (Atom span atom) = 
  case L.findIndex (== atom) expected of
    Just _ -> return atom
    Nothing -> Left $ errAtSpan span $
                 "expected one of |" ++
                 L.intercalate ", " expected ++
                 "|. Found |" ++ show atom ++ "|"


tuplehd:: (AST -> Either Error a) -> AST -> Either Error a
tuplehd f atom@(Atom span _) = 
  Left $ errAtSpan span $ "expected tuple, found atom." ++
            "|" ++ astPretty atom ++ "|"
tuplehd f (Tuple span delim (x:xs)) = f x


tupletail:: (AST -> Either Error a) -> AST -> Either Error [a]
tupletail _ atom@(Atom span _) = 
  Left $ errAtSpan span $ "expected tuple, found atom." ++
            "|" ++ astPretty atom ++ "|"
tupletail f (Tuple span delim (x:xs)) = do
  M.forM xs f 

tuplecadr :: (AST -> Either Error a) -> AST -> Either Error a
tuplecadr f ast = ((!! 0) <$> tupletail pure ast) >>= f
