-- 37_solveSudoku.idr
-- idris2 version

module Main

import Data.List
import Data.Vect
import Data.Strings
import Data.Maybe

data Cell = Fixed Int | Possible (List Int)

Eq Cell where
    (==) (Fixed a) (Fixed a') = a == a'
    (==) (Possible a) (Possible a') = a == a'
    (==) _ _ = False

Grid : Type
Grid = List (List Cell)

initSudoku : List (List Int)
initSudoku = [[6, 0, 0, 0, 0, 0, 0, 1, 0],
                [4, 0, 0, 0, 0, 0, 0, 0, 0],
                [0, 2, 0, 0, 0, 0, 0, 0, 0],
                [0, 0, 0, 0, 5, 0, 4, 0, 7],
                [0, 0, 8, 0, 0, 0, 3, 0, 0],
                [0, 0, 1, 0, 9, 0, 0, 0, 0],
                [3, 0, 0, 4, 0, 0, 2, 0, 0],
                [0, 5, 0, 1, 0, 0, 0, 0, 0],
                [0, 0, 0, 8, 0, 6, 0, 0, 0]]

createGrid : List (List Int) -> Grid
createGrid [] = []
createGrid (x :: xs) = createRow x :: createGrid xs
    where
        createRow : List Int -> List Cell
        createRow [] = []
        createRow (y :: ys) = createCell y :: createRow ys
            where
                createCell : Int -> Cell
                createCell 0 = Possible [1..9]
                createCell x = Fixed x

readGrid : String -> Maybe Grid
readGrid s with (length s == 81)
    readGrid s | False = Nothing
    readGrid s | True  = traverse (traverse readCell) (map unpack (chunksOfStr 9 s))
    where
        readCell : Char -> Maybe Cell
        readCell '.' = Just $ Possible [1..9]
        readCell c with (isDigit c)
            readCell c | True = Just . Fixed $ cast c - cast '0'
            readCell c | False = Nothing

        chunksOfStr : Nat -> String -> List (String)
        chunksOfStr _ "" = []
        chunksOfStr n s = map pack (chunksOf n (unpack s))
        where
            chunksOf : Nat -> List a -> List (List a)
            chunksOf _ [] = []
            chunksOf n x = take n x :: chunksOf n (drop n x)

showGrid : Grid -> String
showGrid = unlines . map (unwords . map showCell)
    where
        showCell : Cell -> String
        showCell (Fixed x) = show x
        showCell _ = "."

isPossible : Cell -> Bool
isPossible (Possible _ ) = True
isPossible _             = False

exclusivePossibilities : List Cell -> List (List Int)
exclusivePossibilities row = elem . filterKey . flipTableKey [] . filterLength . flipPossibleTable . 
    filter (isPossible . snd) $ zip [1..9] row
    where
        insertWith : Eq k => (a -> a -> a) -> k -> a -> List (k, a) -> List (k, a)
        insertWith f i v [] = [(i, v)]
        insertWith f i v (x@(y, z) :: xs) = if i == y then (y, f v z) :: xs
                                                else x :: (insertWith f i v xs)

        flipPossibleTable : List (Int, Cell) -> List (Int, List Int)
        flipPossibleTable = foldl (\acc, (i, Possible xs) => 
                    foldl (\acc', x => insertWith (++) x [i] acc') acc xs) []

        filterLength : List (Int, List Int) -> List (Int, List Int)
        filterLength = filter ((<4) . natToInteger . length . snd)

        flipTableKey :  List (List Int, List Int) -> List (Int, List Int) 
                            -> List (List Int, List Int)
        flipTableKey l [] = l
        flipTableKey l (x@(y,z) :: xs) = flipTableKey (insertWith (++) z [y] l) xs

        filterKey : List (List a, List a) -> List (List a, List a)
        filterKey [] = []
        filterKey (x@(y, z) :: xs) = if length y == length z then x :: filterKey xs
                                        else filterKey xs

        elem : List (List a, List a) -> List (List a)
        elem []               = []
        elem (x@(y, z) :: xs) = z :: elem xs

makeCell : List Int -> Maybe Cell
makeCell ys = case ys of []  => Nothing
                         [y] => Just $ Fixed y
                         _   => Just $ Possible ys

pruneCellsByFixed : List Cell -> Maybe (List Cell)
pruneCellsByFixed cells = traverse pruneCell cells
    where
        pruneCell : Cell -> Maybe Cell
        pruneCell (Possible xs) = makeCell (deleteTmp xs (fixedsTmp cells))
            where
                deleteTmp : List Int -> List Int -> List Int
                deleteTmp [] _      = []
                deleteTmp x []      = x
                deleteTmp x (y::ys) = deleteTmp (delete y x) ys

                fixedsTmp : List Cell -> List Int
                fixedsTmp [] = []
                fixedsTmp (x::xs) = case x of
                                    Fixed y => y :: fixedsTmp xs
                                    Possible y => fixedsTmp xs
        pruneCell x             = Just x

pruneCellsByExclusives : List Cell -> Maybe (List Cell)
pruneCellsByExclusives cells = case exclusives of
                                    [] => Just cells
                                    _  => traverse pruneCell cells
    where
        exclusives : List (List Int)
        exclusives = exclusivePossibilities cells

        pruneCell : Cell -> Maybe Cell
        pruneCell cell@(Fixed _) = Just cell
        pruneCell cell@(Possible xs) = 
            let intersection = intersect xs $ concat exclusives in
                if elem intersection exclusives then makeCell intersection
                    else Just cell

pruneCells : List Cell -> Maybe (List Cell)
pruneCells cells = 
    fixM pruneCellsByFixed cells >>= fixM pruneCellsByExclusives
    where
        fixM : (List Cell -> Maybe (List Cell)) -> 
            List Cell -> Maybe (List Cell)
        fixM f x = f x >>= \x' => if x' == x then Just x else fixM f x'

pruneRows : Grid -> Maybe Grid
pruneRows = traverse pruneCells
        
pruneCols : Grid -> Maybe Grid
pruneCols = map transpose . pruneRows . transpose

subGridsToRowsHelper : Nat -> Grid -> Grid
subGridsToRowsHelper _ [] = []
subGridsToRowsHelper n x = (toRowHelper . transpose) (take n x) ++ 
                            subGridsToRowsHelper n (drop n x)
    where
        toRowHelper : Grid -> Grid
        toRowHelper [] = []
        toRowHelper x = (matToRow . transpose) (take n x) :: toRowHelper (drop n x)
            where
                matToRow : Grid -> List Cell
                matToRow [] = []
                matToRow (x::xs) = x ++ matToRow xs

subGridsToRows : Grid -> Grid
subGridsToRows = subGridsToRowsHelper 3

pruneSubGrids : Grid -> Maybe Grid
pruneSubGrids = map subGridsToRows . pruneRows . subGridsToRows

pruneGrid' : Grid -> Maybe Grid
pruneGrid' grid = pruneRows grid >>= pruneCols >>= pruneSubGrids

pruneGrid : Grid -> Maybe Grid
pruneGrid = fixM pruneGrid'
    where
        fixM : (Grid -> Maybe Grid) -> Grid -> Maybe Grid
        fixM f x = f x >>= \x' => if x' == x then Just x else fixM f x'

nextGrids : Grid -> (Grid, Grid)
nextGrids grid = 
    let (i, first@(Fixed _), rest) =
        fixCell . minimumPossible . filter (isPossible . snd) . zip (take 100 [0..]) . 
        concat $ grid
    in (replace2D i first grid, replace2D i rest grid)
    where
        isPossible : Cell -> Bool
        isPossible (Possible _) = True
        isPossible _            = False

        minimumPossible : List (Int, Cell) -> (Int, Cell)
        minimumPossible [] = (0, Possible (take 10 [1..]))
        minimumPossible (x :: []) = x
        minimumPossible (x :: y :: ys) = 
            if (possibilityCount . snd) x <= (possibilityCount . snd) y then
                minimumPossible (x :: ys)
            else minimumPossible (y :: ys)
            where
                possibilityCount : Cell -> Nat
                possibilityCount (Possible xs) = length xs
                possibilityCount (Fixed _)     = 1

        fixCell : (Int, Cell) -> (Int, Cell, Cell)
        fixCell (i, Possible [x,y])  = (i, Fixed x, Fixed y)
        fixCell (i, Possible (x::xs)) = (i, Fixed x, Possible xs)
        -- fixCell _                    = show "Impossible case"
        fixCell (i, Fixed x)          = (i, Fixed x, Fixed x)

        replace2D : Int -> a -> List (List a) -> List (List a)
        replace2D i v =
            let (x, y) = (div i 9, mod i 9) in replace x (replace y (const v))
            where
                replace : Int -> (b -> b) -> List b -> List b
                replace p f xs = let ys = zip xs (take 100 [0..]) in
                    map (\x => if p == snd x then f (fst x) else fst x) ys

isGridFilled : Grid -> Bool
isGridFilled grid = all isCellFilled (concat grid)
    where
        isCellFilled : Cell -> Bool
        isCellFilled (Fixed _) = True
        isCellFilled (Possible _) = False

isGridInvalid : Grid -> Bool
isGridInvalid grid = any isRowInvalid grid || 
                    any isRowInvalid (transpose grid) ||
                    any isRowInvalid (subGridsToRows grid)
    where
        isRowInvalid : List Cell -> Bool
        isRowInvalid row = let rowInt = fixedsTmp row 
                               rowFilter = filter (\x => x<10 && x>0) (fixedsTmp row) in
                            any (==0) rowInt || length rowFilter /= length (nub rowFilter)
            where
                fixedsTmp : List Cell -> List Int
                fixedsTmp [] = []
                fixedsTmp (x::xs) = case x of
                                    Fixed y => y :: fixedsTmp xs
                                    Possible [] => 0 :: fixedsTmp xs
                                    Possible x  => 10 :: fixedsTmp xs
                                    -- Possible y => (take 9 [1..9]) ++ fixedsTmp xs

solve : Grid -> Maybe Grid
solve grid = pruneGrid grid >>= solve'
    where
        solve' : Grid -> Maybe Grid
        solve' g = if isGridInvalid g then Nothing else
                    if isGridFilled g then Just g else
                        let (grid1, grid2) = nextGrids g
                            in solve grid1 <|> solve grid2

partial
main : IO()
main = do putStrLn "Please input the soduku:"
          inputs <- getLine
          case readGrid inputs of
            Nothing => putStrLn "Invalid input"
            -- Just g  => putStrLn $ showGrid g
            Just g => case solve g of
                Nothing => putStrLn "No solution found"
                Just g' => putStrLn $ showGrid g'
          


