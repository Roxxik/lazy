module Main (main) where

  import Prelude hiding (filter)

  import Data.Maybe
  import Data.List
  import Data.Functor
  import Data.Function
  import Data.Set(Set)
  import qualified Data.Set as Set
  import Data.Heap hiding (filter, null)

  import qualified Data.Map as Map

  import Control.Arrow
  import Control.Applicative
  import Control.Monad

  import System.IO

  data Tree k a = Node  {
        rootLabel :: a,         -- ^ label value
        subForest :: Forest k a -- ^ zero or more child trees
  } deriving (Show)

  type Forest k a = [(k, Tree k a)]

  -- | Build a tree from a seed value
  unfoldTree :: (b -> (a, [(k, b)])) -> b -> Tree k a
  unfoldTree f b = let (a, bs) = f b in Node a (unfoldForest f bs)

  -- | Build a forest from a list of seed values
  unfoldForest :: (b -> (a, [(k, b)])) -> [(k, b)] -> [(k, Tree k a)]
  unfoldForest f = map (second (unfoldTree f))

  type Score = Int
  type Value = Int

  data Direction = NorthEast | SouthEast | SouthWest | NorthWest
    deriving (Show, Eq, Ord)

  type Slot = (Int, Int, Direction)

  data Bag = Bag
    { bWidth :: Int
    , bHeight :: Int
    , bSlots :: Set Slot
    , bBag :: [[Bool]]
    , bIntersectionsHor :: Set Int
    , bIntersectionsVer :: Set Int
    } deriving (Show)

  data Item = Item
    { iIndex :: Int
    , iWidth :: Int
    , iHeight :: Int
    , iValue :: Value
    , iEff :: Double
    } deriving (Show)

  data Problem = Problem
    { pBags :: [Bag]
    , pItems :: [Item]
    , pFill :: Value
    , pScore :: Score
    } deriving (Show)

  data Step = Step
    { sBag :: Int
    , sX :: Int
    , sY :: Int
    , sIndex :: Int
    } deriving (Show)

  mkCoords :: Int -> Int -> [(Int, Int)]
  mkCoords w h = (,) <$> [0..w - 1] <*> [0..h - 1]

  -- parsing
  parse :: (String,String,String) -> Problem
  parse (p,i,f) = Problem (map mkBag . read $ p) (sortBy (compare `on` (iEff)) . zipWith item [0..] . read $ i) (read f) 0

  mkInitSlots :: Int -> Int -> Set Slot
  mkInitSlots w h = Set.fromList [(0,0,SouthEast),(0, w, SouthWest), (w, h, NorthWest), (0, h, NorthEast)]

  mkBag :: (Int,Int) -> Bag
  mkBag (w,h) = Bag w h (mkInitSlots w h) (replicate h (replicate w True)) (Set.fromList [0, w]) (Set.fromList [0, h])

  item :: Int -> (Int,Int,Int) -> Item
  item i (w,h,v) = Item i w h v (fromIntegral v / fromIntegral (w * h))

  -- building possible Solutions
  buildTree :: Problem -> Tree Step Problem
  buildTree = unfoldTree $ \p -> (p, mapMaybe (\s -> (,) s <$> step p s) (mkSteps p))

  mkSteps :: Problem -> [Step]
  mkSteps p = concatMap (mkSteps' (pItems p)) (zip [0..] (pBags p))

  mkSteps' :: [Item] -> (Int, Bag) -> [Step]
  mkSteps' is (bi,b) = uncurry mkStep <$> zip (repeat bi) (Set.toList (bSlots b)) <*> is

  slotToCoord :: (Int,Int) -> Slot -> (Int, Int)
  slotToCoord (_, _) (i, j, SouthEast) = (i,     j)
  slotToCoord (w, _) (i, j, SouthWest) = (i - w, j)
  slotToCoord (w, h) (i, j, NorthWest) = (i - w, j - h)
  slotToCoord (_, h) (i, j, NorthEast) = (i,     j - h)

  mkStep :: Int -> Slot -> Item -> Step
  mkStep b s it = Step b i' j' (iIndex it)
    where (i', j') = slotToCoord (iWidth it,iHeight it) s

  update :: Problem -> [Item] -> Score -> Int -> Bag -> Problem
  update (Problem bags items fill score) is s bi b = Problem (alterList bi b bags) is fill (score + s)

  alterList :: Int -> a -> [a] -> [a]
  alterList n _ [] = error $ "alterList: Index " ++ show n ++ " out of bounds"
  alterList 0 a (x:xs) = a : xs
  alterList n a (x:xs) = x : alterList (n-1) a xs

  takeItem :: Int -> [Item] -> Maybe (Item, [Item])
  takeItem _ [] = Nothing
  takeItem n (i:is)
    | n == iIndex i = Just (i, is)
    | otherwise     = second (i:) <$> takeItem n is

  step :: Problem -> Step -> Maybe Problem
  step p s = fmap (update p is (iValue i) (sBag s)) (step' ((pBags p) !! (sBag s)) (sX s, sY s) i)
    where (i, is) = fromJust (takeItem (sIndex s) (pItems p)) -- assume the steps we generated only contain valid indices

  addCoords :: (Int, Int) -> (Int, Int) -> (Int, Int)
  addCoords (a,b) (c,d) = (a + c, b + d)

  placeable :: (Int, Int) -> (Int, Int) -> [[Bool]] -> Bool
  placeable (i,j) (w,h) b = j >= 0 && i >= 0 && j < h && i < w && b !! j !! i

  place :: (Int, Int) -> [(Int,Int)] -> [[Bool]] -> Maybe [[Bool]]
  place _ [] b = Just b
  place (w,h) ((i,j):cs) b
    | placeable (i,j) (w,h) b = place (w,h) cs $ placeSingle (i,j) b
    | otherwise   = Nothing

  --inedx MUST be in bounds
  placeSingle :: (Int, Int) -> [[Bool]] -> [[Bool]]
  placeSingle (i,j) bss = let bs = alterList i False (bss !! j) in alterList j bs bss

  setBag :: Bag -> [[Bool]] -> Bag
  setBag (Bag w h s _ ih iv) b = Bag w h s b ih iv

  setSlots :: Bag -> Set Slot -> Bag
  setSlots (Bag w h _ b ih iv) s = Bag w h s b ih iv

  setIntersectionsHor :: Bag -> Set Int -> Bag
  setIntersectionsHor (Bag w h s b _ iv) ih = Bag w h s b ih iv

  setIntersectionsVer :: Bag -> Set Int -> Bag
  setIntersectionsVer (Bag w h s b ih _) iv = Bag w h s b ih iv

  step' :: Bag -> (Int,Int) -> Item -> Maybe Bag
  step' b (i,j) it = (\b' -> updateBag b' (i,j) (iWidth it, iHeight it)) . setBag b <$> place (bWidth b, bHeight b) cs (bBag b)
    where cs = map (addCoords (i,j)) (mkCoords (iWidth it) (iHeight it))

  updateBag :: Bag -> (Int, Int) -> (Int, Int) -> Bag
  updateBag b (i,j) (w,h) = setIntersectionsVer b . Set.union ver . bIntersectionsVer . setIntersectionsHor b . Set.union hor . bIntersectionsHor . setSlots b . Set.filter ((\pos -> placeable pos (bWidth b, bHeight b) (bBag b)) . slotToCoord (1,1)) . Set.union newSlots . bSlots $ b
    where
      (newSlots, (hor, ver)) = generateSlots b (i,j) (w,h)

  generateSlots :: Bag -> (Int, Int) -> (Int, Int) -> (Set Slot, (Set Int, Set Int))
  generateSlots b (i,j) (w,h) = (Set.unions . Set.toList $ Set.union (Set.map mkSlots (mkIntersections newHor (bIntersectionsVer b))) (Set.map mkSlots (mkIntersections newVer (bIntersectionsHor b))), (newHor, newVer))
    where
      newHor = Set.fromList [i, i + w]
      newVer = Set.fromList [j, j + h]

  mkIntersections :: Set Int -> Set Int -> Set (Int, Int)
  mkIntersections a  b = Set.fromList ((,) <$> Set.toList a <*> Set.toList b)

  mkSlots :: (Int, Int) -> Set Slot
  mkSlots (i,j) = Set.fromList [(i,j,NorthEast), (i,j,NorthWest), (i,j,SouthWest),(i,j,SouthEast)]

  -- collecting Solutions, contains all the intelligence, just an A*
  collect :: Tree Step Problem -> [(Score, [Step])]
  collect t = (s, []) : (map (second reverse) . collect' $ singleton (f, ([], subForest t)))
    where
      s = getScore . rootLabel $ t
      f = fromIntegral s + (heuristic . rootLabel $ t)

  type Hiep = MaxPrioHeap Int ([Step], [(Step, Tree Step Problem)])

  collect' :: Hiep -> [(Score, [Step])]
  collect' h = case view h of
    Nothing -> []
    Just ((_, next), h') -> let (s, hs) = unzip . uncurry expandAll $ next in s ++ (collect' . unions $ h' : hs)

  expandAll :: [Step] -> [(Step, Tree Step Problem)] -> [((Score, [Step]), Hiep)]
  expandAll = map . expand

  expand :: [Step] -> (Step, Tree Step Problem) -> ((Score, [Step]), Hiep)
  expand steps (next, t) = ((s,steps'), singleton (f, (steps', subForest t)))
    where
      steps' = next : steps
      s = getScore . rootLabel $ t
      f = fromIntegral s + (heuristic . rootLabel $ t)

  heuristic :: Problem -> Int
  heuristic p = heuristic' (freeP p) (map (\i -> (iWidth i * iHeight i, iValue i)) (pItems p))

  heuristic' :: Int -> [(Int, Int)] -> Int
  heuristic' _ [] = 0
  heuristic' n ((s,v):xs)
    | s <= n = v + heuristic' (n - s) xs
    | otherwise = heuristic' n xs

  -- helper functions
  getScore :: Problem -> Score
  getScore p = (pScore p) + negate (pFill p) * freeP p

  freeP :: Problem -> Int
  freeP p = sum (map (sum . map (\b -> if b then 1 else 0) . concat . (bBag)) (pBags p))

  monotonize :: Ord a => a -> [(a, b)] -> [(a, b)]
  monotonize _ [] = []
  monotonize z ((a,s):xs)
    | a > z = (a,s) : monotonize a xs
    | otherwise = monotonize z xs

  showSteps :: Int -> [Step] -> [[(Int, Int, Int)]]
  showSteps bagCount steps = map snd . sortBy (compare `on` fst) . flip (unionBy ((==) `on` fst)) (zip [0..bagCount - 1] (repeat [])) . map (fst . head &&& map snd) . groupBy ((==) `on` fst) . sortBy (compare `on` fst) $ map (\s -> (sBag s, (sX s, sY s, sIndex s))) steps
  -- sortBy ((==) `on` fst) . flip (unionBy ((==) `on` fst)) (zip [0..bagCount - 1] (repeat [])) .
  --Map.toAscList . Map.unionWith (flip const) (Map.fromList (zip [0..bagCount - 1] (repeat []))). Map.fromList
  main :: IO ()
  main = do
    p <- getLine
    i <- getLine
    f <- getLine
    let problem = parse (p,i,f)
    mapM_ ((\s -> print s >> hFlush stdout) . snd . second (showSteps (length (pBags problem)))) . monotonize (minBound :: Score) . collect . buildTree $ problem
