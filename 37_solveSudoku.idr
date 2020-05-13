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

chunksOf : Nat -> List a -> List (List a)
chunksOf _ [] = []
chunksOf n x = take n x :: chunksOf n (drop n x)

chunksOfStr : Nat -> String -> List (String)
chunksOfStr _ "" = []
chunksOfStr n s = map pack (chunksOf n (unpack s))

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

showGrid : Grid -> String
showGrid = unlines . map (unwords . map showCell)
    where
        showCell : Cell -> String
        showCell (Fixed x) = show x
        showCell _ = "."

printGrid : Grid -> IO()
printGrid [] = putStrLn " "
printGrid (x :: xs) = do printRow (fixedsTmp x)
                         putStrLn ""
                         printGrid xs
    where
        fixedsTmp : List Cell -> List Int
        fixedsTmp [] = []
        fixedsTmp (x::xs) = case x of
                            Fixed y => y :: fixedsTmp xs
                            Possible y => 0 :: fixedsTmp xs
        
        printRow : List Int -> IO()
        printRow [] = putStrLn ""
        printRow (x :: xs) = do putStr (show x ++ " ")
                                printRow xs

delete : List Int -> List Int -> List Int
delete = foldl (flip deleteby)
    where 
        deleteby : Int -> List Int -> List Int
        deleteby _ [] = []
        deleteby x (y::ys) = if x == y then ys else y :: (deleteby x ys)

pruneCells : List Cell -> Maybe (List Cell)
pruneCells cells = traverse pruneCell cells
    where
        pruneCell : Cell -> Maybe Cell
        pruneCell (Possible xs) = case delete xs (fixedsTmp cells) of
            []  => Nothing
            [y] => Just $ Fixed y
            ys  => Just $ Possible ys
            where
                fixedsTmp : List Cell -> List Int
                fixedsTmp [] = []
                fixedsTmp (x::xs) = case x of
                                    Fixed y => y :: fixedsTmp xs
                                    Possible y => fixedsTmp xs
        pruneCell x = Just x

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
        toRowHelper x = [(matToRow . transpose) (take n x)] ++ toRowHelper (drop n x)
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

tmpGrid : Grid
tmpGrid = [[Fixed 1, Fixed 2, Fixed 3, Fixed 4], [Fixed 3, Fixed 4, Fixed 1, Fixed 2],
            [Fixed 2, Fixed 1, Fixed 4, Fixed 3], [Fixed 4, Fixed 3, Fixed 2, Possible []]]

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
          


