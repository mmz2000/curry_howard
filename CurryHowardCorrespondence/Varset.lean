--- arbitary character likes to ease the process

inductive propVarNames: Type
| p: propVarNames
| q: propVarNames
| r: propVarNames
| s: propVarNames

def propVarNames.eq: propVarNames → propVarNames → Bool
| propVarNames.p, propVarNames.p => true
| propVarNames.q, propVarNames.q => true
| propVarNames.r, propVarNames.r => true
| propVarNames.s, propVarNames.s => true
| _, _ => false

instance : BEq propVarNames := ⟨propVarNames.eq⟩

def propVarNames.toString: propVarNames → String
| propVarNames.p => "p"
| propVarNames.q => "q"
| propVarNames.r => "r"
| propVarNames.s => "s"

inductive typeVarNames: Type
| w: typeVarNames
| x: typeVarNames
| y: typeVarNames
| z: typeVarNames

def typeVarNames.eq: typeVarNames → typeVarNames → Bool
| typeVarNames.w, typeVarNames.w => true
| typeVarNames.x, typeVarNames.x => true
| typeVarNames.y, typeVarNames.y => true
| typeVarNames.z, typeVarNames.z => true
| _, _ => false

instance : BEq typeVarNames := ⟨typeVarNames.eq⟩

def typeVarNames.toString: typeVarNames → String
| typeVarNames.w => "w"
| typeVarNames.x => "x"
| typeVarNames.y => "y"
| typeVarNames.z => "z"

inductive termVarNames: Type
| W: termVarNames
| X: termVarNames
| Y: termVarNames
| Z: termVarNames

def termVarNames.eq: termVarNames → termVarNames → Bool
| termVarNames.W, termVarNames.W => true
| termVarNames.X, termVarNames.X => true
| termVarNames.Y, termVarNames.Y => true
| termVarNames.Z, termVarNames.Z => true
| _, _ => false

instance : BEq termVarNames := ⟨termVarNames.eq⟩

def termVarNames.toString: termVarNames → String
| termVarNames.W => "W"
| termVarNames.X => "X"
| termVarNames.Y => "Y"
| termVarNames.Z => "Z"
