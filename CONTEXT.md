# Dungeon Crawl

A turn-based roguelike played in the terminal. Its reason to exist is the no-softlock theorem: every dungeon the game produces can be finished, and nothing the player does can change that.

## Language

### World

**Dungeon**:
A single grid of cells that the player explores from a starting cell to the Stairs. The first version has one dungeon per game.
_Avoid_: Level, map, floor

**Cell**:
One position in the dungeon grid.
_Avoid_: Tile, square

**Room**:
A rectangular block of open cells placed by the generator. Keys, Monsters and the Stairs sit in rooms.
_Avoid_: Chamber, area

**Corridor**:
A one-cell-wide path of open cells joining two Rooms. Doors sit where a corridor meets a room.
_Avoid_: Hallway, passage, tunnel

**Passable**:
A cell the player is allowed to enter in the current state.

**Free**:
A cell the player can walk onto without changing anything: floor, Stairs, a Key cell already emptied, or an Open door.

**Wall**:
A cell that is never passable.

**Door**:
A cell with a Color. Entering it spends one Key of that Color, after which the door is Open and stays passable without a key.
_Avoid_: Lock, gate

**Color**:
The label shared by a Door and the Keys that open it. A dungeon may use several colors.
_Avoid_: Kind, type, id

**Key**:
An item with a Color lying in a cell. Picking it up empties the cell. It opens one Door of its Color and is spent doing so.

**Stairs**:
The goal cell. Entering it finishes the dungeon.
_Avoid_: Exit, goal

**Monster**:
A stationary creature occupying a cell. Attacking it costs it Hit Points and it strikes back. Monsters are outside the completability model: dying is not a Softlock.
_Avoid_: Enemy, mob

**Hit Points**:
The health of the player or a Monster. Reaching zero kills them; the player's death ends the game.
_Avoid_: Health, HP in prose

**Fallback dungeon**:
A fixed dungeon the game uses when generation gives up. It is Completable like any other.
_Avoid_: Default dungeon, backup

### Theorem

**Completable**:
A dungeon state is completable when some sequence of moves reaches the Stairs, counting keys picked up and spent along the way.
_Avoid_: Solvable, winnable

**Softlock**:
A reachable game state that is not Completable. The theorem says no softlock exists.
_Avoid_: Stuck, dead end

**Legal move**:
A step in one of four directions, or a wait. Stepping onto a Key picks it up, stepping into a closed Door of a held Color spends a key and opens it, and stepping into a Monster attacks instead of moving. Opening a Door is refused when it would leave the state not Completable. Every legal move must preserve Completable.
_Avoid_: Action, command, turn
