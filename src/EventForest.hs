module EventForest where
import Semantics

-- Searchable mapping from UID of the parent and position in list of siblings
-- to a child event.
type EventForest = [(UID, [(Int, Event)])]

isRoot :: Event -> Bool
isRoot (RootEvent _ _) = True
isRoot _               = False

mkEventForest :: Trace -> EventForest
mkEventForest trc = map children trc
  where children e = let j = eventUID e
                     in (j, map    (\c -> (parentPosition . eventParent $ c, c))
                          $ filter (\e' -> j == (parentUID . eventParent) e') chds)
        chds = filter (not . isRoot) trc

data InfixOrPrefix = Infix | Prefix

data Location = Trunk | ArgumentOf Location | ResultOf Location | FieldOf Int Location
  deriving Eq

instance Show Location where 
   show Trunk            = ""
   show (ArgumentOf loc) = 'a' : show loc
   show (ResultOf   loc) = 'r' : show loc
   show (FieldOf n  loc) = 'f' : show n ++ show loc

data ArgOrRes = Arg | Res

-- Is the first location in the argument, or result subtree of the second location?
argOrRes :: Location -> Location -> ArgOrRes
argOrRes (ArgumentOf loc') loc = if loc == loc' then Arg else argOrRes loc' loc
argOrRes (ResultOf loc')   loc = if loc == loc' then Res else argOrRes loc' loc
argOrRes Trunk             _   = error $ "argOrRes: Second location is not on the path"
                                       ++ "between root and the first location."

type Visit a = Maybe Event -> Location -> a -> a

idVisit :: Visit a
idVisit _ _ z = z

-- Given an event, return the list of (expected) children in depth-first order.
--
-- Nothing indicates that we expect an event (e.g. the argument of an application-
-- event) but it was not there.
--
-- An abstraction (LamEvent) can have more than one application. There is no
-- particular ordering and we just return the applications (AppEvents) in the
-- order we find them in the trace (i.e. evaluation order).

dfsChildren :: EventForest -> Event -> [Maybe Event]
dfsChildren frt e = case e of
    EnterEvent{}              -> byPosition [1]
    RootEvent{}               -> byPosition [1]
    ConstEvent{eventLength=l} -> byPosition [1..l]
    LamEvent{}                -> map (Just . snd) cs
    AppEvent{}                -> byPosition [1,2]

  where -- Find list of events by position
        byPosition :: [ParentPosition] -> [Maybe Event]
        byPosition = map (\pos -> lookup pos cs)

        -- Events in the frt that list our event as parent (in no particular order).
        cs :: [(ParentPosition,Event)]
        cs = case lookup (eventUID e) frt of (Just cs') -> cs'; _ -> []

        
dfsFold :: InfixOrPrefix -> Visit a -> Visit a -> a 
        -> Location -> (Maybe Event) -> EventForest -> a

dfsFold ip pre post z loc me frt 
  = post me loc $ case me of
      Nothing -> z'

      (Just (AppEvent _ _)) -> let [arg,res] = cs
        in case ip of
          Prefix -> csFold $ zip cs [ArgumentOf loc,ResultOf loc]
          Infix  -> let z1 = dfsFold ip pre post z (ArgumentOf loc) arg frt
                        z2 = pre me loc z1
                    in  dfsFold ip pre post z2 (ResultOf loc) res frt

      (Just ConstEvent{}) -> csFold $ zip cs $ map (\i -> FieldOf i loc) [1..]

      _ -> csFold $ zip cs (repeat loc)

  where z'  = pre me loc z

        cs :: [Maybe Event]
        cs = case me of (Just e) -> dfsChildren frt e; Nothing -> error "dfsFold filter failed"

        csFold = foldl (\z'' (c,loc') -> dfsFold ip pre post z'' loc' c frt) z'

treeUIDs :: EventForest -> Event -> [UID]
treeUIDs frt = (map eventUID) . eventsInTree frt

-- Given an event r, return depth first ordered list of events in the (sub)tree starting from r.
eventsInTree :: EventForest -> Event -> [Event]
eventsInTree frt r = reverse $ dfsFold Prefix add idVisit [] Trunk (Just r) frt
  where add (Just e) _ es = e : es
        add Nothing  _ es = es

-- Find all toplevel AppEvents for RootEvent r
topLevelApps :: EventForest -> Event -> [Event]
topLevelApps frt r@RootEvent{} = case dfsChildren frt r of
  [Just ent] -> case dfsChildren frt ent of
    [Just lam] -> case dfsChildren frt lam of [] -> []; as -> map (\(Just a) -> a) as
    _          -> []
  _          -> []
