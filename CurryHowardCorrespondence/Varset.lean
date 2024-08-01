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

instance provpvarbeq : BEq propVarNames := ⟨propVarNames.eq⟩

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

instance typevarbeq: BEq typeVarNames := ⟨typeVarNames.eq⟩

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

instance termvarbeq : BEq termVarNames := ⟨termVarNames.eq⟩

def termVarNames.toString: termVarNames → String
| termVarNames.W => "W"
| termVarNames.X => "X"
| termVarNames.Y => "Y"
| termVarNames.Z => "Z"

def typeVarNames.fromPropVarNames: propVarNames → typeVarNames
| propVarNames.p => typeVarNames.w
| propVarNames.q => typeVarNames.x
| propVarNames.r => typeVarNames.y
| propVarNames.s => typeVarNames.z

theorem eq_pvname_eq_tvname_: ∀ {p q}, p.eq q → (typeVarNames.fromPropVarNames p).eq (typeVarNames.fromPropVarNames q):= by
  intro p q h
  cases p
  cases q
  simp [typeVarNames.fromPropVarNames]
  simp [typeVarNames.eq]
  simp [propVarNames.eq] at h
  simp [propVarNames.eq] at h
  simp [propVarNames.eq] at h
  cases q
  simp [propVarNames.eq] at h
  simp [typeVarNames.fromPropVarNames]
  simp [typeVarNames.eq]
  simp [propVarNames.eq] at h
  simp [propVarNames.eq] at h
  cases q
  simp [propVarNames.eq] at h
  simp [propVarNames.eq] at h
  simp [typeVarNames.fromPropVarNames]
  simp [typeVarNames.eq]
  simp [propVarNames.eq] at h
  cases q
  simp [propVarNames.eq] at h
  simp [propVarNames.eq] at h
  simp [propVarNames.eq] at h
  simp [typeVarNames.fromPropVarNames]
  simp [typeVarNames.eq]

theorem eq_tvname_eq_pvname_: ∀ {p q}, (typeVarNames.fromPropVarNames p).eq (typeVarNames.fromPropVarNames q) → p.eq q := by
  intro p q h
  cases p
  cases q
  simp [propVarNames.eq]
  simp [typeVarNames.fromPropVarNames] at h
  simp [typeVarNames.eq] at h
  simp [typeVarNames.fromPropVarNames] at h
  simp [typeVarNames.eq] at h
  simp [typeVarNames.fromPropVarNames] at h
  simp [typeVarNames.eq] at h
  cases q
  simp [typeVarNames.fromPropVarNames] at h
  simp [typeVarNames.eq] at h
  simp [propVarNames.eq]
  simp [typeVarNames.fromPropVarNames] at h
  simp [typeVarNames.eq] at h
  simp [typeVarNames.fromPropVarNames] at h
  simp [typeVarNames.eq] at h
  cases q
  simp [typeVarNames.fromPropVarNames] at h
  simp [typeVarNames.eq] at h
  simp [typeVarNames.fromPropVarNames] at h
  simp [typeVarNames.eq] at h
  simp [propVarNames.eq]
  simp [typeVarNames.fromPropVarNames] at h
  simp [typeVarNames.eq] at h
  cases q
  simp [typeVarNames.fromPropVarNames] at h
  simp [typeVarNames.eq] at h
  simp [typeVarNames.fromPropVarNames] at h
  simp [typeVarNames.eq] at h
  simp [typeVarNames.fromPropVarNames] at h
  simp [typeVarNames.eq] at h
  simp [propVarNames.eq]

theorem eq_pvname_eq_tvname: ∀ {p q}, p == q → (typeVarNames.fromPropVarNames p) == (typeVarNames.fromPropVarNames q):= by
  intro p q h
  simp [provpvarbeq] at h
  simp [typevarbeq]
  rw [eq_pvname_eq_tvname_]
  exact h

theorem eq_tvname_eq_pvname: ∀ {p q}, (typeVarNames.fromPropVarNames p) == (typeVarNames.fromPropVarNames q) → p == q := by
  intro p q h
  simp [typevarbeq] at h
  simp [provpvarbeq]
  rw [eq_tvname_eq_pvname_]
  exact h

def typeVarNames.toPropVarNames: typeVarNames → propVarNames
| typeVarNames.w =>  propVarNames.p
| typeVarNames.x =>  propVarNames.q
| typeVarNames.y =>  propVarNames.r
| typeVarNames.z =>  propVarNames.s

theorem eq_tvname_eq_pvname2: ∀ {p q:typeVarNames}, p==q → p.toPropVarNames == q.toPropVarNames := by
  intro p q h
  simp [typevarbeq] at h
  simp [provpvarbeq]
  cases q
  cases p
  simp [typeVarNames.toPropVarNames]
  simp [propVarNames.eq]
  simp [typeVarNames.eq] at h
  simp [typeVarNames.eq] at h
  simp [typeVarNames.eq] at h
  cases p
  simp [typeVarNames.eq] at h
  simp [typeVarNames.toPropVarNames]
  simp [propVarNames.eq]
  simp [typeVarNames.eq] at h
  simp [typeVarNames.eq] at h
  cases p
  simp [typeVarNames.eq] at h
  simp [typeVarNames.eq] at h
  simp [typeVarNames.toPropVarNames]
  simp [propVarNames.eq]
  simp [typeVarNames.eq] at h
  cases p
  simp [typeVarNames.eq] at h
  simp [typeVarNames.eq] at h
  simp [typeVarNames.eq] at h
  simp [typeVarNames.toPropVarNames]
  simp [propVarNames.eq]

theorem eq_pvname_eq_tvname2: ∀ {p q:typeVarNames}, p.toPropVarNames == q.toPropVarNames → p==q := by
  intro p q h
  simp [typevarbeq]
  simp [provpvarbeq] at h
  cases p
  cases q
  simp [typeVarNames.eq]
  simp [typeVarNames.toPropVarNames,propVarNames.eq] at h
  simp [typeVarNames.toPropVarNames,propVarNames.eq] at h
  simp [typeVarNames.toPropVarNames,propVarNames.eq] at h
  cases q
  simp [typeVarNames.toPropVarNames,propVarNames.eq] at h
  simp [typeVarNames.eq]
  simp [typeVarNames.toPropVarNames,propVarNames.eq] at h
  simp [typeVarNames.toPropVarNames,propVarNames.eq] at h
  cases q
  simp [typeVarNames.toPropVarNames,propVarNames.eq] at h
  simp [typeVarNames.toPropVarNames,propVarNames.eq] at h
  simp [typeVarNames.eq]
  simp [typeVarNames.toPropVarNames,propVarNames.eq] at h
  cases q
  simp [typeVarNames.toPropVarNames,propVarNames.eq] at h
  simp [typeVarNames.toPropVarNames,propVarNames.eq] at h
  simp [typeVarNames.toPropVarNames,propVarNames.eq] at h
  simp [typeVarNames.eq]


def termVarNames.fromPropVarNames: propVarNames → termVarNames
| propVarNames.p => termVarNames.W
| propVarNames.q => termVarNames.X
| propVarNames.r => termVarNames.Y
| propVarNames.s => termVarNames.Z

theorem eq_pvname_eq_tname: ∀ {p q}, p == q → (termVarNames.fromPropVarNames p) == (termVarNames.fromPropVarNames q):= by
  intro p q h
  simp [termvarbeq]
  simp [provpvarbeq] at h
  cases p
  cases q
  simp [termVarNames.fromPropVarNames]
  simp [termVarNames.eq]
  simp [propVarNames.eq] at h
  simp [propVarNames.eq] at h
  simp [propVarNames.eq] at h
  cases q
  simp [propVarNames.eq] at h
  simp [termVarNames.fromPropVarNames]
  simp [termVarNames.eq]
  simp [propVarNames.eq] at h
  simp [propVarNames.eq] at h
  cases q
  simp [propVarNames.eq] at h
  simp [propVarNames.eq] at h
  simp [termVarNames.fromPropVarNames]
  simp [termVarNames.eq]
  simp [propVarNames.eq] at h
  cases q
  simp [propVarNames.eq] at h
  simp [propVarNames.eq] at h
  simp [propVarNames.eq] at h
  simp [termVarNames.fromPropVarNames]
  simp [termVarNames.eq]

theorem eq_tname_eq_pvname: ∀ {p q}, (termVarNames.fromPropVarNames p)== (termVarNames.fromPropVarNames q) → p ==q := by
  intro p q h
  simp [termvarbeq] at h
  simp [provpvarbeq]
  cases p
  cases q
  simp [propVarNames.eq]
  simp [termVarNames.fromPropVarNames] at h
  simp [termVarNames.eq] at h
  simp [termVarNames.fromPropVarNames] at h
  simp [termVarNames.eq] at h
  simp [termVarNames.fromPropVarNames] at h
  simp [termVarNames.eq] at h
  cases q
  simp [termVarNames.fromPropVarNames] at h
  simp [termVarNames.eq] at h
  simp [propVarNames.eq]
  simp [termVarNames.fromPropVarNames] at h
  simp [termVarNames.eq] at h
  simp [termVarNames.fromPropVarNames] at h
  simp [termVarNames.eq] at h
  cases q
  simp [termVarNames.fromPropVarNames] at h
  simp [termVarNames.eq] at h
  simp [termVarNames.fromPropVarNames] at h
  simp [termVarNames.eq] at h
  simp [propVarNames.eq]
  simp [termVarNames.fromPropVarNames] at h
  simp [termVarNames.eq] at h
  cases q
  simp [termVarNames.fromPropVarNames] at h
  simp [termVarNames.eq] at h
  simp [termVarNames.fromPropVarNames] at h
  simp [termVarNames.eq] at h
  simp [termVarNames.fromPropVarNames] at h
  simp [termVarNames.eq] at h
  simp [propVarNames.eq]


def termVarNames.toPropVarNames: termVarNames → propVarNames
| termVarNames.W =>  propVarNames.p
| termVarNames.X =>  propVarNames.q
| termVarNames.Y =>  propVarNames.r
| termVarNames.Z =>  propVarNames.s

theorem eq_tname_eq_pvname2: ∀ {p q:termVarNames}, p==q → p.toPropVarNames == q.toPropVarNames := by
  intro p q h
  simp [termvarbeq] at h
  simp [provpvarbeq]
  cases q
  cases p
  simp [termVarNames.toPropVarNames]
  simp [propVarNames.eq]
  simp [termVarNames.eq] at h
  simp [termVarNames.eq] at h
  simp [termVarNames.eq] at h
  cases p
  simp [termVarNames.eq] at h
  simp [termVarNames.toPropVarNames]
  simp [propVarNames.eq]
  simp [termVarNames.eq] at h
  simp [termVarNames.eq] at h
  cases p
  simp [termVarNames.eq] at h
  simp [termVarNames.eq] at h
  simp [termVarNames.toPropVarNames]
  simp [propVarNames.eq]
  simp [termVarNames.eq] at h
  cases p
  simp [termVarNames.eq] at h
  simp [termVarNames.eq] at h
  simp [termVarNames.eq] at h
  simp [termVarNames.toPropVarNames]
  simp [propVarNames.eq]

theorem eq_pvname_eq_tname2: ∀ {p q:termVarNames}, p.toPropVarNames == q.toPropVarNames → p==q := by
  intro p q h
  simp [termvarbeq]
  simp [provpvarbeq] at h
  cases p
  cases q
  simp [termVarNames.eq]
  simp [termVarNames.toPropVarNames,propVarNames.eq] at h
  simp [termVarNames.toPropVarNames,propVarNames.eq] at h
  simp [termVarNames.toPropVarNames,propVarNames.eq] at h
  cases q
  simp [termVarNames.toPropVarNames,propVarNames.eq] at h
  simp [termVarNames.eq]
  simp [termVarNames.toPropVarNames,propVarNames.eq] at h
  simp [termVarNames.toPropVarNames,propVarNames.eq] at h
  cases q
  simp [termVarNames.toPropVarNames,propVarNames.eq] at h
  simp [termVarNames.toPropVarNames,propVarNames.eq] at h
  simp [termVarNames.eq]
  simp [termVarNames.toPropVarNames,propVarNames.eq] at h
  cases q
  simp [termVarNames.toPropVarNames,propVarNames.eq] at h
  simp [termVarNames.toPropVarNames,propVarNames.eq] at h
  simp [termVarNames.toPropVarNames,propVarNames.eq] at h
  simp [termVarNames.eq]
