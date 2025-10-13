#![feature(step_trait)]

pub mod dimacs;
pub mod fol;
mod utils;

use ahash::AHasher;
pub use utils::*;

use std::{
    cmp::Ordering,
    collections::HashSet,
    fmt::{self, Debug, Display},
    hash::{Hash, Hasher},
    iter::Step,
    ops::{Add, AddAssign, Deref, DerefMut, Not},
    vec,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Var(pub u32);

impl Var {
    #[inline]
    pub fn new(x: usize) -> Self {
        Self(x as _)
    }

    #[inline]
    pub fn lit(&self) -> Lit {
        Lit(self.0 << 1)
    }
}

impl Add<u32> for Var {
    type Output = Var;

    #[inline]
    fn add(self, rhs: u32) -> Self::Output {
        Self(self.0 + rhs)
    }
}

impl AddAssign<u32> for Var {
    #[inline]
    fn add_assign(&mut self, rhs: u32) {
        self.0 += rhs;
    }
}

impl From<Lit> for Var {
    #[inline]
    fn from(value: Lit) -> Self {
        value.var()
    }
}

impl From<u32> for Var {
    #[inline]
    fn from(value: u32) -> Self {
        Self(value)
    }
}

impl From<i32> for Var {
    #[inline]
    fn from(value: i32) -> Self {
        Self(value as u32)
    }
}

impl From<usize> for Var {
    #[inline]
    fn from(value: usize) -> Self {
        Self(value as u32)
    }
}

impl From<Var> for u32 {
    #[inline]
    fn from(value: Var) -> Self {
        value.0
    }
}

impl From<Var> for i32 {
    #[inline]
    fn from(value: Var) -> Self {
        value.0 as i32
    }
}

impl From<Var> for usize {
    #[inline]
    fn from(value: Var) -> Self {
        value.0 as usize
    }
}

impl Deref for Var {
    type Target = u32;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Display for Var {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Step for Var {
    #[inline]
    fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>) {
        u32::steps_between(&start.0, &end.0)
    }

    #[inline]
    fn forward_checked(start: Self, count: usize) -> Option<Self> {
        u32::forward_checked(start.0, count).map(|v| Self(v))
    }

    #[inline]
    fn backward_checked(start: Self, count: usize) -> Option<Self> {
        u32::backward_checked(start.0, count).map(|v| Self(v))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Lit(u32);

impl From<Var> for Lit {
    #[inline]
    fn from(value: Var) -> Self {
        Self(value.0 << 1)
    }
}

impl From<Lit> for u32 {
    #[inline]
    fn from(val: Lit) -> Self {
        val.0
    }
}

impl From<Lit> for i32 {
    #[inline]
    fn from(val: Lit) -> Self {
        let mut v: i32 = val.var().into();
        if !val.polarity() {
            v = -v;
        }
        v
    }
}

impl From<i32> for Lit {
    #[inline]
    fn from(value: i32) -> Self {
        Self::new(Var(value.unsigned_abs()), value > 0)
    }
}

impl Lit {
    #[inline]
    pub fn new(var: Var, polarity: bool) -> Self {
        Lit(var.0 + var.0 + !polarity as u32)
    }

    #[inline]
    pub fn var(&self) -> Var {
        Var(self.0 >> 1)
    }

    #[inline]
    pub fn polarity(&self) -> bool {
        self.0 & 1 == 0
    }

    #[inline]
    pub fn constant_lit(polarity: bool) -> Self {
        Self::new(Var::new(0), !polarity)
    }

    #[inline]
    pub fn is_constant(&self, polarity: bool) -> bool {
        *self == Self::constant_lit(polarity)
    }

    #[inline]
    pub fn not_if(&self, c: bool) -> Self {
        if c {
            !*self
        } else {
            *self
        }
    }
}

impl Not for Lit {
    type Output = Self;

    #[inline]
    fn not(mut self) -> Self::Output {
        self.0 ^= 1;
        self
    }
}

impl Debug for Lit {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.polarity() {
            write!(f, "{}", self.var())
        } else {
            write!(f, "-{}", self.var())
        }
    }
}

impl Display for Lit {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self, f)
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Clause {
    lits: Vec<Lit>,
}

impl Clause {
    pub fn new() -> Self {
        Clause { lits: Vec::new() }
    }

    #[inline]
    pub fn ordered_intersection(&self, other: &Clause) -> Vec<Lit> {
        debug_assert!(self.is_sorted_by_key(|l| l.var()));
        debug_assert!(other.is_sorted_by_key(|l| l.var()));
        let mut res = Vec::new();
        let mut i = 0;
        for l in self.iter() {
            while i < other.len() && other[i] < *l {
                i += 1;
            }
            if i == other.len() {
                break;
            }
            if *l == other[i] {
                res.push(*l);
            }
        }
        res
    }

    #[inline]
    pub fn resolvent(&self, other: &Clause, v: Var) -> Clause {
        let mut new: Clause = other.iter().filter(|l| l.var() != v).copied().collect();
        let other_set: HashSet<Lit> = HashSet::from_iter(new.iter().copied());
        for x in self.iter().filter(|l| l.var() != v) {
            if other_set.contains(&!*x) {
                return Clause::default();
            } else if !other_set.contains(x) {
                new.push(*x);
            }
        }
        new
    }
}

impl Default for Clause {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for Clause {
    type Target = Vec<Lit>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.lits
    }
}

impl DerefMut for Clause {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.lits
    }
}

impl AsRef<[Lit]> for Clause {
    #[inline]
    fn as_ref(&self) -> &[Lit] {
        self.as_slice()
    }
}

impl Not for Clause {
    type Output = Cube;

    #[inline]
    fn not(self) -> Self::Output {
        let lits = self.lits.iter().map(|lit| !*lit).collect();
        Cube { lits }
    }
}

impl Not for &Clause {
    type Output = Cube;

    #[inline]
    fn not(self) -> Self::Output {
        let lits = self.lits.iter().map(|lit| !*lit).collect();
        Cube { lits }
    }
}

impl<F: Into<Vec<Lit>>> From<F> for Clause {
    fn from(value: F) -> Self {
        Self { lits: value.into() }
    }
}

impl FromIterator<Lit> for Clause {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            lits: Vec::from_iter(iter),
        }
    }
}

impl IntoIterator for Clause {
    type Item = Lit;

    type IntoIter = vec::IntoIter<Lit>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.lits.into_iter()
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Cube {
    lits: Vec<Lit>,
}

impl Cube {
    #[inline]
    pub fn new() -> Self {
        Cube { lits: Vec::new() }
    }

    #[inline]
    pub fn subsume(&self, cube: &Cube) -> bool {
        let x_lit_set = self.iter().collect::<HashSet<&Lit>>();
        let y_lit_set = cube.iter().collect::<HashSet<&Lit>>();
        x_lit_set.is_subset(&y_lit_set)
    }

    #[inline]
    pub fn ordered_subsume(&self, cube: &Cube) -> bool {
        debug_assert!(self.is_sorted_by_key(|l| l.var()));
        debug_assert!(cube.is_sorted_by_key(|l| l.var()));
        if self.len() > cube.len() {
            return false;
        }
        let mut j = 0;
        for i in 0..self.len() {
            while j < cube.len() && self[i].0 > cube[j].0 {
                j += 1;
            }
            if j == cube.len() || self[i] != cube[j] {
                return false;
            }
        }
        true
    }

    #[inline]
    pub fn ordered_subsume_execpt_one(&self, cube: &Cube) -> (bool, Option<Lit>) {
        debug_assert!(self.is_sorted_by_key(|l| l.var()));
        debug_assert!(cube.is_sorted_by_key(|l| l.var()));
        let mut diff = None;
        if self.len() > cube.len() {
            return (false, None);
        }
        let mut j = 0;
        for i in 0..self.len() {
            while j < cube.len() && self[i].var() > cube[j].var() {
                j += 1;
            }
            if j == cube.len() {
                return (false, None);
            }
            if self[i] != cube[j] {
                if diff == None && self[i].var() == cube[j].var() {
                    diff = Some(self[i]);
                } else {
                    return (false, None);
                }
            }
        }
        (diff.is_none(), diff)
    }

    #[inline]
    pub fn intersection(&self, cube: &Cube) -> Cube {
        let x_lit_set = self.iter().collect::<HashSet<&Lit>>();
        let y_lit_set = cube.iter().collect::<HashSet<&Lit>>();
        Self {
            lits: x_lit_set
                .intersection(&y_lit_set)
                .copied()
                .copied()
                .collect(),
        }
    }

    #[inline]
    pub fn ordered_intersection(&self, cube: &Cube) -> Cube {
        debug_assert!(self.is_sorted_by_key(|l| l.var()));
        debug_assert!(cube.is_sorted_by_key(|l| l.var()));
        let mut res = Cube::new();
        let mut i = 0;
        for l in self.iter() {
            while i < cube.len() && cube[i] < *l {
                i += 1;
            }
            if i == cube.len() {
                break;
            }
            if *l == cube[i] {
                res.push(*l);
            }
        }
        res
    }
}

impl Default for Cube {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for Cube {
    type Target = Vec<Lit>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.lits
    }
}

impl DerefMut for Cube {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.lits
    }
}

impl PartialOrd for Cube {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Cube {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        debug_assert!(self.is_sorted_by_key(|x| x.var()));
        debug_assert!(other.is_sorted_by_key(|x| x.var()));
        let min_index = self.len().min(other.len());
        for i in 0..min_index {
            match self[i].0.cmp(&other[i].0) {
                Ordering::Less => return Ordering::Less,
                Ordering::Equal => {}
                Ordering::Greater => return Ordering::Greater,
            }
        }
        self.len().cmp(&other.len())
    }
}

impl Not for Cube {
    type Output = Clause;

    #[inline]
    fn not(self) -> Self::Output {
        let lits = self.lits.iter().map(|lit| !*lit).collect();
        Clause { lits }
    }
}

impl Not for &Cube {
    type Output = Clause;

    #[inline]
    fn not(self) -> Self::Output {
        let lits = self.lits.iter().map(|lit| !*lit).collect();
        Clause { lits }
    }
}

impl<const N: usize> From<[Lit; N]> for Cube {
    #[inline]
    fn from(s: [Lit; N]) -> Self {
        Self { lits: Vec::from(s) }
    }
}

impl From<&[Lit]> for Cube {
    #[inline]
    fn from(s: &[Lit]) -> Self {
        Self { lits: Vec::from(s) }
    }
}

impl From<Cube> for Vec<Lit> {
    #[inline]
    fn from(val: Cube) -> Self {
        val.lits
    }
}

impl FromIterator<Lit> for Cube {
    #[inline]
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            lits: Vec::from_iter(iter),
        }
    }
}

impl IntoIterator for Cube {
    type Item = Lit;

    type IntoIter = std::vec::IntoIter<Lit>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.lits.into_iter()
    }
}

impl AsRef<[Lit]> for Cube {
    #[inline]
    fn as_ref(&self) -> &[Lit] {
        self.as_slice()
    }
}

impl Display for Cube {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.lits.fmt(f)
    }
}

#[derive(Debug, Default, Clone)]
pub struct Lemma {
    cube: Cube,
    sign: u128,
    hash: u64,
}

impl Deref for Lemma {
    type Target = Cube;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.cube
    }
}

impl DerefMut for Lemma {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.cube
    }
}

impl PartialEq for Lemma {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if self.hash != other.hash || self.sign != other.sign || self.len() != other.len() {
            return false;
        }
        for i in 0..self.cube.len() {
            if self[i] != other[i] {
                return false;
            }
        }
        true
    }
}

impl Eq for Lemma {}

impl PartialOrd for Lemma {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Lemma {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.cube.cmp(&other.cube)
    }
}

impl Lemma {
    #[inline]
    pub fn new(mut cube: Cube) -> Self {
        cube.sort();
        let mut sign = 0;
        for l in cube.iter() {
            sign |= 1 << (Into::<u32>::into(*l) % u128::BITS);
        }
        let mut hasher = AHasher::default();
        cube.hash(&mut hasher);
        Self {
            cube,
            sign,
            hash: hasher.finish(),
        }
    }

    #[inline]
    pub fn cube(&self) -> &Cube {
        &self.cube
    }

    #[inline]
    fn var_sign(&self) -> u128 {
        ((self.sign >> 1) | self.sign) & 113427455640312821154458202477256070485_u128
    }

    #[inline]
    pub fn subsume(&self, other: &Lemma) -> bool {
        if self.cube.len() > other.cube.len() {
            return false;
        }
        if self.sign & other.sign != self.sign {
            return false;
        }
        self.cube.ordered_subsume(&other.cube)
    }

    #[inline]
    pub fn subsume_execpt_one(&self, other: &Lemma) -> (bool, Option<Lit>) {
        if self.cube.len() > other.cube.len() {
            return (false, None);
        }
        let ss = self.var_sign();
        if ss & other.var_sign() != ss {
            return (false, None);
        }
        self.cube.ordered_subsume_execpt_one(&other.cube)
    }

    #[inline]
    pub fn subsume_set(&self, other: &Lemma, other_lits: &LitSet) -> bool {
        if self.cube.len() > other.cube.len() {
            return false;
        }
        if self.sign & other.sign != self.sign {
            return false;
        }
        for l in self.iter() {
            if !other_lits.has(*l) {
                return false;
            }
        }
        true
    }
}

impl Hash for Lemma {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hash.hash(state);
    }
}

pub fn cnf_lits_and(master: Lit, lits: &[Lit]) -> Vec<Clause> {
    let mut cnf = Vec::new();
    let mut cls = Clause::from([master]);
    for l in lits.iter() {
        cnf.push(Clause::from([!master, *l]));
        cls.push(!*l);
    }
    cnf.push(cls);
    cnf
}

pub fn cnf_lits_or(master: Lit, lits: &[Lit]) -> Vec<Clause> {
    let mut cnf = Vec::new();
    let mut cls = Clause::from([!master]);
    for l in lits.iter() {
        cnf.push(Clause::from([master, !*l]));
        cls.push(*l);
    }
    cnf.push(cls);
    cnf
}

impl Display for Lemma {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.cube, f)
    }
}
