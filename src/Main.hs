{-# LANGUAGE ImplicitParams #-}

-- ABC logic puzzle

module Main where

import Control.Monad
import Data.List
import Data.Array.IArray
import MiniSat
import Safe
import System.Environment

import System.Random.Shuffle
import System.Random

type Puzzle = Array Int (Array Int Field) -- rows of columns
type Field = Array Int Lit
data Hints = Hints {
      top, right, bottom, left :: Array Int Field}


data Full = Full { puzzle :: Puzzle, hints :: Hints}

genLit :: (?solver :: Solver) => IO Lit
genLit = newLit ?solver

replicateAM :: Monad m => Int -> m a -> m (Array Int a)
replicateAM l m = liftM (listArray (0,l-1)) (replicateM l m)

replicateA :: Int -> a -> Array Int a
replicateA l m = listArray (0,l-1) (replicate l m)

generateAM :: Monad m => Int -> (Int -> m a) -> m (Array Int a)
generateAM l f =  liftM (listArray (0,l')) (mapM f [0..l'])
    where l' = l-1

genField :: (?letters :: Int, ?solver :: Solver) => IO Field
genField = replicateAM (?letters+1) genLit

genPuzzle :: (?size :: Int, ?letters :: Int, ?solver :: Solver) => IO Puzzle
genPuzzle = replicateAM ?size $ replicateAM ?size genField

genHints :: (?size :: Int, ?letters :: Int, ?solver :: Solver) => IO Hints
genHints = liftM4 Hints side side side side
    where side = replicateAM ?size genField

genFull :: (?size :: Int, ?letters :: Int, ?solver :: Solver) => IO Full
genFull = liftM2 Full genPuzzle genHints

addClause' :: (?solver :: Solver) => [Lit] -> IO ()
addClause' c = addClause ?solver c >> return ()

addClauses :: (?solver :: Solver) => [[Lit]] -> IO ()
addClauses = mapM_ addClause'

lx :: (?letters :: Int) => [Int]
lx = [1 .. ?letters]

fx :: (?letters :: Int) => [Int]
fx = [0 .. ?letters]

sx :: (?size :: Int) => [Int]
sx = [0 .. ?size - 1]

sx_reverse :: (?size :: Int) => [Int]
sx_reverse = [?size - 1, (?size - 2).. 0]


conHint :: (?letters :: Int, ?solver :: Solver) => Field  -- ^ hint field
        -> [Field] -- ^ neighbouring fields, the closest field is last
                   -- in the list
        -> IO ()
conHint hint neigh = addClauses[ hint ! l :  hint ! 0 : neg (f ! l) : blanks r 
                                 | l <- lx, (f:r)<- init $ tails neigh]
    where blanks = map (\f -> neg (f!0))


conBottomHints :: (?size :: Int, ?letters :: Int, ?solver :: Solver) => Array Int Field -> Puzzle -> IO ()
conBottomHints h p = sequence_ [conHint (h!i) [(p!j)!i|j<-[(?letters-1) .. (?size-1)]]| i <- sx]
                     >> mapM_ conField (elems h)

conRightHints :: (?size :: Int, ?letters :: Int, ?solver :: Solver) => Array Int Field -> Puzzle -> IO ()
conRightHints h p = sequence_ [conHint (h!i) [(p!i)!j|j<-[(?letters-1) .. (?size-1)]]| i <- sx]
                     >> mapM_ conField (elems h)

conTopHints :: (?size :: Int, ?letters :: Int, ?solver :: Solver) => Array Int Field -> Puzzle -> IO ()
conTopHints h p = sequence_ [conHint (h!i) [(p!j)!i|j<-[(?size - ?letters),(?size - ?letters - 1) .. 0]]| i <- sx]
                     >> mapM_ conField (elems h)

conLeftHints :: (?size :: Int, ?letters :: Int, ?solver :: Solver) => Array Int Field -> Puzzle -> IO ()
conLeftHints h p = sequence_ [conHint (h!i) [(p!i)!j|j<-[(?size - ?letters),(?size - ?letters - 1) .. 0]]| i <- sx]
                     >> mapM_ conField (elems h)

conHints :: (?size :: Int, ?letters :: Int, ?solver :: Solver) => Full -> IO ()
conHints (Full p h) = conBottomHints (bottom h) p >> conRightHints (right h) p
             >> conTopHints (top h) p >> conLeftHints (left h) p

conFull :: (?size :: Int, ?letters :: Int, ?solver :: Solver) => Full -> IO ()
conFull full = conPuzzle (puzzle full) >> conHints full

conField :: (?letters :: Int, ?solver :: Solver) => Field -> IO ()
conField l = do addClause' $ elems l
                addClauses [ [neg (l!i), neg (l!j)] | i <- fx, j <- [0 .. i-1]]

conFields :: (?size :: Int, ?letters :: Int, ?solver :: Solver) => Puzzle -> IO ()
conFields p = sequence_ [conField ((p!i)!j) | i <- sx, j <- sx]

-- fields must be different letters (however, both can be blank)
conDiffFields :: (?letters :: Int, ?solver :: Solver) => Field -> Field -> IO ()
conDiffFields l1 l2 = do 
  addClauses [[neg (l1!i), neg (l2!i)] | i <- lx]

conRows :: (?size :: Int, ?letters :: Int, ?solver :: Solver) => Puzzle  -> IO ()
conRows p = do
  -- fields must be different letters
  sequence_ [conDiffFields (r!i) (r!j) | r <- elems p, i <- sx, j <- [0..i-1]] 
  -- each letter must appear
  addClauses [[(r!i)!l | i <- sx] | r <- elems p, l <- lx]

conColumns :: (?size :: Int, ?letters :: Int, ?solver :: Solver) => Puzzle  -> IO ()
conColumns p = do 
  -- letters must be different letters
  sequence_ [conDiffFields ((p!i)!c) ((p!j)!c) | c <- sx, i <- sx, j <- [0..i-1]]
  -- each letter must appear
  addClauses [[((p!i!)c)!l | i <- sx] | c <- sx, l <- lx]

conPuzzle :: (?size :: Int, ?letters :: Int, ?solver :: Solver) => Puzzle -> IO ()
conPuzzle p = conRows p >> conColumns p >> conFields p


-- generate contstraits that avoid ambiguous configurations
conAmbFields :: (?solver::Solver,?size::Int,?letters::Int) => Puzzle -> IO ()
conAmbFields p = when (?size >= 2) $
      addClauses =<< sequence 
                   [ liftM (map neg [(((p!i)!j)!l), (((p!di)!dj)!l), (((p!i)!dj)!f), (((p!di)!j)!f)] ++) 
                   (if f==0 then halfVis i j di dj else fullVis i j di dj)
                   | i <- range, j <- range, di<-[0..i-1]++[i+1..(?size-1)]
                   , dj<-[j+1..(?size-1)], l <- lx, f<- fx, l/=f]

    where range = [0..(?size-2)]
          low = ?size - ?letters + 1
          hi = ?letters - 1
          halfVis :: Int -> Int -> Int -> Int -> IO [Lit]
          halfVis i j i' j' = liftM concat $ sequence [getVis i j i' j', getVis i' j' i j]
          fullVis :: Int -> Int -> Int -> Int -> IO [Lit]
          fullVis i j i' j' = liftM concat $ sequence [getVis i j i' j', getVis i' j' i j,
                                                       getVis i j' i' j, getVis i' j i j']
          getVis i j i' j' = if i < low || j < low || i >= hi || j >= hi
                             then do 
                               lit <- genLit 
                               con lit i j i' j'
                               return [lit]
                             else return []
          when' True x = liftM (:[]) x
          when' False _ = return []
          con lit i j di dj = 
            let left = when' (i < low && di > i) $ do
                          vis <- genLit 
                          addClauses [[neg vis, ((p!i')!j)!0] |i'<-[0..i-1]]
                          addClause' (neg vis : [neg (((p!i')!j)!0) | i'<-[i+1..di]])
                          return vis
                top = when' (j < low && dj > j) $ do
                          vis <- genLit 
                          addClauses [[neg vis, ((p!i)!j')!0] |j'<-[0..j-1]]
                          addClause' (neg vis : [neg (((p!i)!j')!0) | j'<-[j+1..dj]])
                          return vis
                bottom = when' (i >= hi && di < i) $ do
                          vis <- genLit 
                          addClauses [[neg vis, ((p!i')!j)!0] |i'<-[i+1..(?size-1)]]
                          addClause' (neg vis : [neg (((p!i')!j)!0) | i'<-[di..i-1]])
                          return vis
                right = when' (j >= hi && dj < j) $ do
                          vis <- genLit 
                          addClauses [[neg vis, ((p!i)!j')!0] |j'<-[j+1..(?size-1)]]
                          addClause' (neg vis : [neg (((p!i)!j')!0) | j'<-[dj..j-1]])
                          return vis
            in do lits <- sequence [left,top,bottom,right]
                  addClause' (neg lit : concat lits)



data Entry = Blank
           | Letter Int

instance Show Entry where
    show Blank = " "
    show (Letter l) = [iterate succ 'A' !! l]

newtype Solution = Solution {unSolution :: Array Int (Array Int (Entry))}

instance Show Solution where
    show = unlines . map (unwords . map show . elems) . elems . unSolution

getSolution :: (?size :: Int, ?letters :: Int, ?solver :: Solver) => Puzzle -> IO Solution
getSolution p = liftM Solution $ liftM (listArray (0,?size-1)) $ 
                sequence [ liftM (listArray (0,?size-1)) $ 
                           sequence [ getEntry f | f <- elems r] | r <- elems p ]

getHints :: (?size :: Int, ?letters :: Int, ?solver :: Solver) => Array Int Field -> IO [Entry]
getHints h = sequence [ getEntry f | f <- elems h]

getAllHints :: Int -> [((Int,Int),Int)] -> AllHints
getAllHints size hints = (AllHints t r b l (length hints))
    where [t,r,b,l] = [ emp // [ (i,Letter (letter-1)) | ((s',i),letter) <- hints, s' == s] | s <- [0..3]]
          emp = replicateA size Blank


data AllHints = AllHints {atop, aright, abottom, aleft :: Array Int Entry, hintSize :: Int} deriving Show

getEntry :: (?letters :: Int, ?solver :: Solver) => Field -> IO Entry
getEntry l = do Just b <- modelValue ?solver (l!0)
                if b then return Blank else getLetter
    where getLetter ::  IO Entry
          getLetter = do res <- mapM (\i -> modelValue ?solver (l!i)) lx 
                         let Just n = findIndex (== Just True) res
                         return $ Letter n

-- Adds clause to avoid the currently found solution.
removeCurrentSolution :: (?solver :: Solver) => IO Bool
removeCurrentSolution = do 
  n <- minisat_num_vars ?solver 
  addClause ?solver =<<
            sequence [(modelValue ?solver lit >>= (\ (Just b) ->
                              return (if b then neg lit else lit)))
                             |  lit <- map (MkLit . fromInteger . toInteger) [0..(n-1)]]


entryToInt :: Entry -> Int
entryToInt Blank = 0
entryToInt (Letter i) = i + 1

removeSolution :: (?size :: Int, ?letters :: Int, ?solver :: Solver, ?full :: Full) => Solution -> IO ()
removeSolution (Solution sol) = addClause' [neg (entryValue ((i,j),entryToInt $ (sol!i)!j))| i<-sx,j<-sx]


prettyHints :: AllHints -> String
prettyHints (AllHints t r b l s) = 
  "  | " ++ (intercalate " | " $ map show $ elems t) ++ " |  \n"
        ++ rule
        ++ intercalate rule rows
        ++ rule
        ++ "  | " ++ (intercalate " | " $ map show $ elems b) ++ " |  \n\n"
        ++ "number of hints: " ++ show s ++ "\n"
    where rule = "--" ++ concat (replicate size "+---") ++ "+--\n"
          divider = concat (replicate size " |  ") ++ " | "
          rows = zipWith (\l r -> show l ++ divider ++ show r ++ "\n") (elems l) (elems r)
          size = length $ indices t

-- complete list of entry positions


search :: Int -> Int -> IO AllHints
search size letters = do 
  solver <- newSolver
  let ?solver = solver
      ?size = size
      ?letters = letters
  f <- genFull
  conFull f
  conAmbFields (puzzle f)
  let ?full = f
  generateConfiguration

generateConfiguration :: (?size :: Int, ?letters :: Int, ?solver :: Solver, ?full :: Full)
                         => IO AllHints
generateConfiguration = do space <- shuffleM [ (i,j) | i <- sx, j<- sx]
                           growPuzzle space []


growPuzzle :: (?size :: Int, ?letters :: Int, ?solver :: Solver, ?full :: Full)
              => [(Int,Int)] -> [((Int,Int),Int)] -> IO AllHints
-- reset search if we hit a hint selection with
-- multiple solutions
growPuzzle [] _ = putStrLn "did not find a puzzle" >> generateConfiguration
growPuzzle (choice:space') entries = do
       letter <- randomRIO (0,?letters)
       let entries' = (choice,letter): entries
       sat <- solve ?solver (map entryValue entries')
       if sat then growPuzzle space' entries'
       else do 
         -- We found an unsatisfiable set of hints.
         True <- solve ?solver (map entryValue entries)
         s@(Solution sol) <- getSolution (puzzle ?full)
         putStrLn "solution:"
         print s
         removeSolution s
         let getLetters i = let soli = sol ! i
                            in [((3,i),getLetter [soli!j | j<- sx]),
                                ((0,i),getLetter [(sol!j)!i | j<-sx]),
                                ((1,i),getLetter [soli!j | j<- sx_reverse]),
                                ((2,i),getLetter [(sol!j)!i | j<-sx_reverse])]
             space = concatMap getLetters sx
         sat <- solve ?solver (map hintValue space)
         if sat then do
                  s <- getSolution (puzzle ?full)
                  putStrLn "alternative:"
                  print s
                  generateConfiguration -- not unique, start again
         else do -- check whether solution is it really unique
                 -- (we excluded some previous solutions)
           deleteSolver ?solver
           solver <- newSolver
           let ?solver = solver
           f <- genFull
           conFull f
           removeSolution s
           sat <- solve ?solver (map hintValue space)
           if sat then   conAmbFields (puzzle f) >> generateConfiguration -- not unique, start again
           else do
             space' <- shuffleM space
             minimize space' []
    where getLetter = foldr getLetterRun (error "Internal error: cannot find letter in solution!")
          getLetterRun Blank r = r
          getLetterRun (Letter l) _ = l + 1
                          

-- turn a hint position and letter into a literal
hintValue :: (?full :: Full) => ((Int, Int), Int) -> Lit
hintValue ((h,i),l) = (([top, right, bottom , left]!! h) (hints ?full) ! i) ! l

entryValue :: (?full :: Full) => ((Int, Int), Int) -> Lit
entryValue ((i,j),l) = (((puzzle ?full) ! i) ! j) ! l


minimize :: (?size :: Int, ?letters :: Int, ?solver :: Solver, ?full :: Full)
            => [((Int, Int), Int)] -> [((Int, Int), Int)] -> IO AllHints
minimize [] result = do
       -- We minimised the set of hints. Now we just verify that we indeed
       -- have a unique solution.
            deleteSolver ?solver
            solver <- newSolver
            let ?solver = solver
            f <- genFull
            conFull f
            let set = map hintValue result
            sat <- solve ?solver set
            when (not sat) (error "solution is wrong: not satisfiable!")
            s <- getSolution (puzzle ?full)
            removeSolution s
            sat' <- solve ?solver set
            when sat' (error "solution is wrong: not unique!")
            return(getAllHints ?size result)
minimize (h: r) acc = do sat' <- solve ?solver (map hintValue (r ++ acc))
                         if sat' then minimize r (h:acc)
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
