{-# LANGUAGE ImplicitParams, ConstraintKinds #-}

-- ABC logic puzzle

module Main where

import Control.Monad
import Data.List
import qualified Data.Vector as Vector
import Data.Vector (Vector, (!),(//))
import MiniSat
import Safe
import System.Environment

import System.Random

type Puzzle = Vector (Vector Field) -- rows of columns
type Field = Vector Lit
data Hints = Hints {
      top, right, bottom, left :: Vector Field}


data Full = Full { puzzle :: Puzzle, hints :: Hints}

type Env = (?size :: Int, ?letters :: Int, ?solver :: Solver)

genLit :: Env => IO Lit
genLit = newLit ?solver


genField :: Env => IO Field
genField = Vector.replicateM (?letters+1) genLit

genPuzzle :: Env => IO Puzzle
genPuzzle = Vector.replicateM ?size $ Vector.replicateM ?size genField

genHints :: Env => IO Hints
genHints = liftM4 Hints side side side side
    where side = Vector.replicateM ?size genField

genFull :: Env => IO Full
genFull = liftM2 Full genPuzzle genHints

addClause' :: Env => [Lit] -> IO Bool
addClause' = addClause ?solver

addClauses :: Env => [[Lit]] -> IO ()
addClauses = mapM_ addClause'

lx :: Env => [Int]
lx = [1 .. ?letters]

fx :: Env => [Int]
fx = [0 .. ?letters]

sx :: Env => [Int]
sx = [0 .. ?size - 1]


conHint :: Env => Field  -- ^ hint field
        -> [Field] -- ^ neighbouring fields, the closest field is last
                   -- in the list
        -> IO ()
conHint hint neigh = addClauses[ hint ! l :  hint ! 0 : neg (f ! l) : blanks r 
                                 | l <- lx, (f:r)<- init $ tails neigh]
    where blanks = map (\f -> neg (f!0))


conBottomHints :: Env => Vector Field -> Puzzle -> IO ()
conBottomHints h p = sequence_ [conHint (h!i) [(p!j)!i|j<-[(?letters-1) .. (?size-1)]]| i <- sx]
                     >> mapM_ conField (Vector.toList h)

conRightHints :: Env => Vector Field -> Puzzle -> IO ()
conRightHints h p = sequence_ [conHint (h!i) [(p!i)!j|j<-[(?letters-1) .. (?size-1)]]| i <- sx]
                     >> mapM_ conField (Vector.toList h)

conTopHints :: Env => Vector Field -> Puzzle -> IO ()
conTopHints h p = sequence_ [conHint (h!i) [(p!j)!i|j<-[(?size - ?letters),(?size - ?letters - 1) .. 0]]| i <- sx]
                     >> mapM_ conField (Vector.toList h)

conLeftHints :: Env => Vector Field -> Puzzle -> IO ()
conLeftHints h p = sequence_ [conHint (h!i) [(p!i)!j|j<-[(?size - ?letters),(?size - ?letters - 1) .. 0]]| i <- sx]
                     >> mapM_ conField (Vector.toList h)

conHints :: Env => Full -> IO ()
conHints (Full p h) = conBottomHints (bottom h) p >> conRightHints (right h) p
             >> conTopHints (top h) p >> conLeftHints (left h) p

conFull :: Env => Full -> IO ()
conFull full = conPuzzle (puzzle full) >> conHints full

conField :: Env => Field -> IO ()
conField l = do addClause' $ Vector.toList l
                addClauses [ [neg (l!i), neg (l!j)] | i <- fx, j <- [0 .. i-1]]

conFields :: Env => Puzzle -> IO ()
conFields p = sequence_ [conField ((p!i)!j) | i <- sx, j <- sx]

-- fields must be different letters (however, both can be blank)
conDiffFields :: Env => Field -> Field -> IO ()
conDiffFields l1 l2 = do 
  addClauses [[neg (l1!i), neg (l2!i)] | i <- lx]

conRows :: Env => Puzzle  -> IO ()
conRows p = do
  -- fields must be different letters
  sequence_ [conDiffFields (r!i) (r!j) | r <- Vector.toList p, i <- sx, j <- [0..i-1]] 
  -- each letter must appear
  addClauses [[(r!i)!l | i <- sx] | r <- Vector.toList p, l <- lx]

conColumns :: Env => Puzzle  -> IO ()
conColumns p = do 
  -- letters must be different letters
  sequence_ [conDiffFields ((p!i)!c) ((p!j)!c) | c <- sx, i <- sx, j <- [0..i-1]]
  -- each letter must appear
  addClauses [[((p!i!)c)!l | i <- sx] | c <- sx, l <- lx]

conPuzzle :: Env => Puzzle -> IO ()
conPuzzle p = conRows p >> conColumns p >> conFields p

data Entry = Blank
           | Letter Int

instance Show Entry where
    show Blank = " "
    show (Letter l) = [iterate succ 'A' !! l]

newtype Solution = Solution {unSolution :: [[Entry]]}

instance Show Solution where
    show = unlines . map (unwords . map show) . unSolution

getSolution :: Env => Puzzle -> IO Solution
getSolution p = liftM Solution $ sequence [ sequence [ getEntry f | f <- Vector.toList r] | r <- Vector.toList p ]

getHints :: Env => Vector Field -> IO [Entry]
getHints h = sequence [ getEntry f | f <- Vector.toList h]

getAllHints :: Int -> [((Int,Int),Int)] -> AllHints
getAllHints size hints = (AllHints t r b l (length hints))
    where [t,r,b,l] = [ emp // [ (i,Letter (letter-1)) | ((s',i),letter) <- hints, s' == s] | s <- [0..3]]       
          emp = Vector.replicate size Blank


data AllHints = AllHints {atop, aright, abottom, aleft :: Vector Entry, hintSize :: Int} deriving Show

getEntry :: Env => Field -> IO Entry
getEntry l = do Just b <- modelValue ?solver (l!0)
                if b then return Blank else getLetter
    where getLetter ::  IO Entry
          getLetter = do res <- mapM (\i -> modelValue ?solver (l!i)) lx 
                         let Just n = findIndex (== Just True) res
                         return $ Letter n

-- To be called after a successful 'solve'. It tries to find another
-- solution.
solveAgain :: Solver -> [Lit] -> IO Bool
solveAgain solver set =  
                     do n <- minisat_num_vars solver 
                        addClause solver =<<
                                  sequence [(modelValue solver lit >>= (\ (Just b) ->
                                                    return (if b then neg lit else lit)))
                                                   |  lit <- map (MkLit . fromInteger . toInteger) [0..(n-1)]]
                        solve solver set


prettyHints :: AllHints -> String
prettyHints (AllHints t r b l s) = " | " ++ (intercalate " | " $ map show $ Vector.toList t) ++ " | \n"
                                   ++ rule
                                   ++ intercalate rule rows
                                   ++ rule
                                   ++ " | " ++ (intercalate " | " $ map show $ Vector.toList b) ++ " | \n\n"
                                   ++ "number of hints: " ++ show s ++ "\n"
    where rule = "-" ++ concat (replicate size "+---") ++ "+-\n"
          divider = concat (replicate size "|   ") ++ "|"
          rows = zipWith (\l r -> show l ++ divider ++ show r ++ "\n") (Vector.toList l) (Vector.toList r)
          size = Vector.length t

type Env' = (Env, ?space :: ([(Int,Int)]), 
             ?hints :: [((Int,Int),Int)], ?full :: Full)

-- complete list of hint positions
hintPositions :: Env => [(Int,Int)]
hintPositions = [ (side,i) | side <- [0..3], i<- sx] :: [(Int,Int)]


search :: Int -> Int -> IO AllHints
search size letters = do 
  solver <- newSolver
  let ?solver = solver
      ?size = size
      ?letters = letters
  f <- genFull
  conFull f
  let ?full = f
      ?space = hintPositions
      ?hints = []
  growHints

growHints :: Env' => IO AllHints
growHints = do case ?space of
                 -- reset search if we hit a hint selection with
                 -- multiple solutions
                 [] -> let ?space = hintPositions
                           ?hints = []
                       in growHints
                 _ -> do
                   (choice, space') <- pick ?space
                   letter <- randomRIO (1,?letters)
                   let hints' = (choice,letter): ?hints
                   sat <- solve ?solver (map hintValue hints')
                   if sat then let ?space = space'
                                   ?hints = hints'
                               in growHints
                   else do 
                     -- We found an unsatisfiable set of hints. We
                     -- backtrack and check whether we found a set of
                     -- hints with a unique solution.
                     let set = map hintValue ?hints
                     solve ?solver set
                     sat <- solveAgain ?solver set
                     if sat then do 
                              -- Solution is not unique. Reset the
                              -- solver and start growing the hints.
                              deleteSolver ?solver
                              solver <- newSolver
                              let ?solver = solver
                              f <- genFull
                              conFull f
                              let ?full = f
                              growHints
                     else minimize ?hints []
-- turn a hint position and letter into a literal
hintValue :: Env' => ((Int, Int), Int) -> Lit
hintValue ((h,i),l) = (([top, right, bottom , left]!! h) (hints ?full) ! i) ! l

pick l = do i <- randomRIO (0,length l -1)
            let (l1, choice:l2) = splitAt i l
            return (choice, l1++l2)

minimize :: Env' => [((Int, Int), Int)] -> [((Int, Int), Int)] -> IO AllHints
minimize [] acc = do 
  -- We minimised the set of hints. Now we just verify that we indeed
  -- have a unique solution.
    deleteSolver ?solver
    solver <- newSolver
    let ?solver = solver
    f <- genFull
    conFull f
    let set = map hintValue acc
    sat <- solve ?solver set
    sat' <- solveAgain ?solver set
    when (not sat || sat') (error "solution is wrong")
    return (getAllHints ?size acc)
minimize (h: r) acc = do sat <- solve ?solver (map hintValue (r ++ acc))
                         if sat then minimize r (h:acc)
                            else minimize r acc


main = do c <- getArgs
          case c of 
            [size,letters] -> 
                case (readMay size, readMay letters) of
                  (Just size, Just letters)
                    | size < letters -> putStrLn "The the number of letters may not be larger than the puzzle size."
                    | letters < 1 -> putStrLn "The the number of letters must be a positive integer"
                    | otherwise -> search size letters >>= (putStr . prettyHints)
                  _ -> usage
            _ -> usage
    where usage = do name <- getProgName
                     putStrLn $ "usage: " ++ name ++ " <puzzle size> <number of letters>"
