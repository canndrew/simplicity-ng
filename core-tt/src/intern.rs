use crate::priv_prelude::*;

pub struct Interner<S: Scheme> {
    tys: RwLock<IndexSet<RawTyKind<S>>>,
    terms: RwLock<IndexSet<RawTmKind<S>>>,
    stucks: RwLock<IndexSet<RawStuckKind<S>>>,
}

pub struct Intern<T> {
    _ph: PhantomData<T>,
    index: usize,
}

pub trait Internable {
    type Scheme: Scheme;
    fn retrieve_clone(interner: &Interner<Self::Scheme>, index: usize) -> Self;
    fn insert(self, interner: &Interner<Self::Scheme>) -> usize;
}

impl<S: Scheme> Interner<S> {
    pub fn new() -> Interner<S> {
        Interner {
            tys: RwLock::new(IndexSet::new()),
            terms: RwLock::new(IndexSet::new()),
            stucks: RwLock::new(IndexSet::new()),
        }
    }
}

impl<S: Scheme, T: Internable<Scheme = S>> Intern<T> {
    pub fn new(val: T) -> Intern<T> {
        let interner = S::interner();
        let index = val.insert(interner);
        Intern {
            _ph: PhantomData,
            index,
        }
    }

    pub fn get_clone(self) -> T
    where
        T: Clone + 'static,
    {
        let interner = S::interner();
        T::retrieve_clone(interner, self.index)
    }
}

impl<S: Scheme> Internable for RawTyKind<S> {
    type Scheme = S;

    fn retrieve_clone(interner: &Interner<S>, index: usize) -> RawTyKind<S> {
        let tys = interner.tys.read().unwrap();
        tys.get_index(index).unwrap().clone()
    }

    fn insert(self, interner: &Interner<S>) -> usize {
        let tys = interner.tys.read().unwrap();
        if let Some(index) = tys.get_index_of(&self) {
            return index;
        }
        drop(tys);
        let mut tys = interner.tys.write().unwrap();
        let (index, _is_new) = tys.insert_full(self);
        index
    }
}

impl<S: Scheme> Internable for RawTmKind<S> {
    type Scheme = S;

    fn retrieve_clone(interner: &Interner<S>, index: usize) -> RawTmKind<S> {
        let terms = interner.terms.read().unwrap();
        terms.get_index(index).unwrap().clone()
    }

    fn insert(self, interner: &Interner<S>) -> usize {
        let terms = interner.terms.read().unwrap();
        if let Some(index) = terms.get_index_of(&self) {
            return index;
        }
        drop(terms);
        let mut terms = interner.terms.write().unwrap();
        let (index, _is_new) = terms.insert_full(self);
        index
    }
}

impl<S: Scheme> Internable for RawStuckKind<S> {
    type Scheme = S;

    fn retrieve_clone(interner: &Interner<S>, index: usize) -> RawStuckKind<S> {
        let stucks = interner.stucks.read().unwrap();
        stucks.get_index(index).unwrap().clone()
    }

    fn insert(self, interner: &Interner<S>) -> usize {
        let stucks = interner.stucks.read().unwrap();
        if let Some(index) = stucks.get_index_of(&self) {
            return index;
        }
        drop(stucks);
        let mut stucks = interner.stucks.write().unwrap();
        let (index, _is_new) = stucks.insert_full(self);
        index
    }
}

impl<T> Clone for Intern<T> {
    fn clone(&self) -> Intern<T> {
        Intern {
            _ph: PhantomData,
            index: self.index,
        }
    }
}

impl<T> Copy for Intern<T> {}

impl<T> PartialEq for Intern<T> {
    fn eq(&self, other: &Intern<T>) -> bool {
        self.index == other.index
    }
}

impl<T> Eq for Intern<T> {
}

impl<T> PartialOrd for Intern<T> {
    fn partial_cmp(&self, other: &Intern<T>) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(&self.index, &other.index)
    }
}

impl<T> Ord for Intern<T> {
    fn cmp(&self, other: &Intern<T>) -> cmp::Ordering {
        Ord::cmp(&self.index, &other.index)
    }
}

impl<T> hash::Hash for Intern<T> {
    fn hash<H>(&self, state: &mut H)
    where
        H: hash::Hasher,
    {
        hash::Hash::hash(&self.index, state)
    }
}

impl<S: Scheme, T: Internable<Scheme = S> + Clone + fmt::Debug + 'static> fmt::Debug for Intern<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let val = self.get_clone();
        <T as fmt::Debug>::fmt(&val, f)
    }
}

unsafe impl<T: Send> Send for Intern<T> {}
unsafe impl<T: Sync> Sync for Intern<T> {}

