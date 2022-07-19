//! Library providing [`UN`] a number of dynamically allocated capacity,encoded in base 10,2 digits 
//! per byte and little endian,[`UNArr`],like [`UN`] but with a generic constant capacity and
//! [`SliceUN`] a custom DST that both previous types deref to.

use ::{
    std::{
        borrow::{Borrow, BorrowMut},
        cmp::Ordering,
        convert::TryFrom,
        error::Error,
        fmt::{self, Debug, Display, Formatter},
        hash::Hash,
        hint::unreachable_unchecked,
        marker::PhantomData,
        mem::MaybeUninit,
        num::ParseIntError,
        ops::{Add, AddAssign, Deref, DerefMut, Mul, MulAssign},
        slice,
        str::FromStr,
    }
};

#[derive(Clone, Hash)]
pub struct UN {
    vec: Vec<u8>
}

impl<T: Deref<Target = SliceUN>> PartialEq<T> for UN {
    fn eq(&self, other: &T) -> bool {
        self.deref().vec.eq(&other.deref().vec)
    } 
}

impl Eq for UN {}

impl<T: Deref<Target = SliceUN>> PartialOrd<T> for UN {
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        self.deref().partial_cmp(other.deref())
    }
}

impl Ord for UN {
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(other.deref())
    }
}

impl UN {
    pub const fn new() -> Self {
        Self {
            vec: Vec::new()
        }
    }
}

impl<T: Deref<Target = SliceUN>> Add<T> for UN {
    type Output = Self;

    fn add(mut self, other: T) -> Self::Output {
        self += other;
        self
    }
}

impl<T: Deref<Target = SliceUN>> AddAssign<T> for UN {
    fn add_assign(&mut self, other: T) {
        let mut b = true;

        let a: &mut UN = unsafe { &mut *(self as *mut _) };
        let len = self.vec.len();
        let mut it1 = self.vec.iter_mut();

        let mut it2len = other.deref().vec.len();
        let mut it2 = other.deref().vec.iter().copied();

        let mut e = if let Some(e3) = it1.next() {
            e3
        } else {
            self.vec.extend(it2);
            return
        };

        let mut e2 = if let Some(e3) = it2.next() {
            e3
        } else {
            return
        };        

        let mut rest = 0;

        loop {
            if b {
                let x = get_1(*e);
                let y = get_1(e2);

                let mut result = x + y + rest;

                rest = 0;

                while result > 9 {
                    rest += 1;
                    result -= 10;                 
                }

                *e = set_1(*e, result);

                b = false;
            } else {
                let x = get_2(*e);
                let y = get_2(e2);

                let mut result = x + y + rest;
                rest = 0;

                while result > 9 {
                    rest += 1;
                    result -= 10;                 
                }

                *e = set_2(*e, result);


                if let Some(e3) = it2.next() {
                    it2len -= 1;
                    e2 = e3;
                } else {
                    if rest > 0 {
                        e2 = rest;
                        rest = 0;
                    } else {
                        break
                    }
                }

                if let Some(e3) = it1.next() {
                    e = e3;
                } else {
                    for _ in 0..((it2len / 2) + 1) {                
                        a.vec.push(0);
                    }

                    let a = unsafe { &mut *(a as *mut UN) };

                    it1 = a.vec[len..].iter_mut();
                    e = it1.next().unwrap()
                }

                b = true;
            }
        }
    }
}

impl<T: Deref<Target = SliceUN>> Mul<T> for UN {
    type Output = Self;

    fn mul(mut self, other: T) -> Self::Output {
        self *= other;
        self
    }
}

impl<T: Deref<Target = SliceUN>> MulAssign<T> for UN {
    fn mul_assign(&mut self, other: T) {
        let mut b = true;

        let a: &mut UN = unsafe { &mut *(self as *mut _) };
        let len = self.vec.len();
        let mut it1 = self.vec.iter_mut();

        let mut it2len = other.deref().vec.len();
        let mut it2 = other.deref().vec.iter().copied();

        let mut e = if let Some(e3) = it1.next() {
            e3
        } else {
            self.vec.extend(it2);
            return
        };

        let mut e2 = if let Some(e3) = it2.next() {
            e3
        } else {
            return
        };        

        let mut rest = 0;

        loop {
            if b {
                let x = get_1(*e);
                let y = get_1(e2);

                let mut result = x * y + rest;

                rest = 0;

                while result > 9 {
                    rest += 1;
                    result -= 10;                 
                }

                *e = set_1(*e, result);

                b = false;
            } else {
                let x = get_2(*e);
                let y = get_2(e2);

                let mut result = x * y + rest;
                rest = 0;

                while result > 9 {
                    rest += 1;
                    result -= 10;                 
                }

                *e = set_2(*e, result);


                if let Some(e3) = it2.next() {
                    it2len -= 1;
                    e2 = e3;
                } else {
                    if rest > 0 {
                        e2 = rest;
                        rest = 0;
                    } else {
                        break
                    }
                }

                if let Some(e3) = it1.next() {
                    e = e3;
                } else {
                    for _ in 0..((it2len / 2) + 1) {                
                        a.vec.push(0);
                    }

                    let a = unsafe { &mut *(a as *mut UN) };

                    it1 = a.vec[len..].iter_mut();
                    e = it1.next().unwrap()
                }

                b = true;
            }
        }
    }
}

impl Display for UN  {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self.deref(), f)
    }
}

impl Debug for UN  {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self.deref(), f)
    }
}

impl Deref for UN {
    type Target = SliceUN;

    fn deref(&self) -> &Self::Target {
        unsafe { &*(&*self.vec as *const _ as *const SliceUN) }
    }
}

impl DerefMut for UN {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *(&mut *self.vec as *mut _ as *mut SliceUN) }
    }
}

impl FromStr for UN {
    type Err = ParseIntError;

    fn from_str(x: &str) -> Result<Self, Self::Err> {
        let mut a = UN::new();

        let mut b = false;

        for c in x.chars().rev() {
            let e = c.to_string().parse::<u8>()?;

            if b {
                let x = a.vec.last_mut().unwrap();

                *x = set_2(*x, e);

                b = false;
            } else {
                a.vec.push(set_1(0, e));
                b = true;
            }
        }

        Ok(a)
    }
}

impl From<u8> for UN {
    fn from(x: u8) -> Self {
        x.to_string().parse().unwrap()
    }
}

impl From<u16> for UN {
    fn from(x: u16) -> Self {
        x.to_string().parse().unwrap()
    }
}

impl From<u32> for UN {
    fn from(x: u32) -> Self {
        x.to_string().parse().unwrap()
    }
}

impl From<u64> for UN {
    fn from(x: u64) -> Self {
        x.to_string().parse().unwrap()
    }
}

impl From<u128> for UN {
    fn from(x: u128) -> Self {
        x.to_string().parse().unwrap()
    }
}

#[derive(PartialEq, Eq)]
pub struct SliceUN {
    vec: [u8]
}

impl SliceUN {
    fn log10(&self) -> usize {
        let len = self.vec.len();

        if len > 0 {
            let a = *self.vec.last().unwrap();

            let x = get_2(a);

            if x > 0 {
                len * 2    
            } else {
                (len * 2) - 1
            }
        } else {
            0
        }    
    }

    fn iter(&self) -> UNIter<'_> {            

        if self.vec.len() > 0 {
            let a = *self.vec.last().unwrap();

            let x = get_2(a);
            UNIter {
                slice: self,
                index: self.vec.len() - 1,
                len: self.log10(),
                get_2: x > 0,
            }
        } else {
            UNIter {
                slice: self,
                index: 0,
                len: 0,
                get_2: true,
            }
        }
    }
}

pub struct UNIter<'a> {
    slice: &'a SliceUN,
    index: usize,
    len: usize,
    get_2: bool,
}

impl<'a> Iterator for UNIter<'a> {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.len -= 1;
            let x = self.slice.vec[self.index];

            Some(if self.get_2 {
                self.get_2 = false;
                get_2(x)
            } else {
                if self.index > 0 {
                    self.index -= 1;
                    self.get_2 = true
                }

                get_1(x)
            })
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a> ExactSizeIterator for UNIter<'a> {
    fn len(&self) -> usize {
        self.len
    }
}

impl PartialOrd for SliceUN {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SliceUN {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut it1 = self.iter();
        let mut it2 = other.iter();

        if it1.len() < it2.len() {
            for _ in 0..it2.len() - it1.len() {
                let a = 0.cmp(
                    &it2.next()
                        .unwrap_or_else(|| unsafe { unreachable_unchecked() }),
                );

                match a {
                    Ordering::Equal => (),
                    _ => return a,
                }
            }
        } else if it1.len() > it2.len() {
            for _ in 0..it1.len() - it2.len() {
                let a = it1
                    .next()
                    .unwrap_or_else(|| unsafe { unreachable_unchecked() })
                    .cmp(&0);

                match a {
                    Ordering::Equal => (),
                    _ => return a,
                }
            }
        }

        it1.cmp(it2)
    }
}


impl Display for SliceUN  {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut it = self.vec.iter().copied().rev();

        if let Some(e) = it.next() {
            let a = get_2(e);

            if a != 0 {
                write!(f, "{}", a)?;
            }

            write!(f, "{}", get_1(e))?;
        } else {
            write!(f, "0")?;
        }

        while let Some(e) = it.next() {
            write!(f, "{}{}", get_2(e), get_1(e))?;
        }

        Ok(())
    }
}

impl Debug for SliceUN  {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

pub struct UNArr<const N: usize> {
    vec: [MaybeUninit<u8>; N],
    len: usize
}

impl<const N: usize> UNArr<N> {
    pub const fn new() -> Self {
        Self {
            vec: [MaybeUninit::uninit(); N],
            len: 0
        }
    }

    fn push(&mut self, x: u8) -> Option<()>  {
        self.vec.get_mut(self.len)?.write(x);
        self.len += 1;
        Some(())
    }

    fn get_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.vec.as_ptr() as *const u8, self.len) }
    }

    fn get_slice_mut(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.vec.as_mut_ptr() as *mut u8, self.len) }
    }

    fn max() -> Self {
        let max_n = set_2(set_1(0, 9), 9);

        Self {
            vec: [MaybeUninit::new(max_n); N],
            len: N
        }
    }
}

impl<const N: usize> Deref for UNArr<N> {
    type Target = SliceUN;

    fn deref(&self) -> &Self::Target {
        unsafe { &*(self.get_slice() as *const _ as *const SliceUN) }
    }
}

impl<const N: usize> DerefMut for UNArr<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *(self.get_slice_mut() as *mut _ as *mut SliceUN) }
    }
}

pub struct NotBigEnough<const N: usize>(PhantomData<[u8; N]>);

impl<const N: usize> Error for NotBigEnough<N> {}

impl<const N: usize> Display for NotBigEnough<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

impl<const N: usize> Debug for NotBigEnough<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{} it's not long enough for the number", N)
    }
}


/// An error generated by [`UNArr::from_str`].
#[derive(Debug)]
pub enum FromStrError<const N: usize> {
    /// This variant means the buffer it's not larger enough.
    NBE(NotBigEnough<N>),
    /// This variant means some character it's not a number.
    ParseInt(ParseIntError),
}

impl<const N: usize> Display for FromStrError<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            FromStrError::NBE(x) => Display::fmt(x, f),
            FromStrError::ParseInt(x) => Display::fmt(x, f),
        }
    }
}

impl<const N: usize> Error for FromStrError<N> {}

impl<const N: usize> FromStr for UNArr<N> {
    type Err = FromStrError<N>;

    fn from_str(x: &str) -> Result<Self, Self::Err> {
        let mut arr = UNArr::new();

        let mut b = false;

        for c in x.chars().rev() {
            let e = c
                    .to_string()
                    .parse::<u8>()
                    .map_err(FromStrError::ParseInt)?;

            if b {
                let x = arr.get_slice_mut().last_mut().unwrap();

                *x = set_2(*x, e);                

                b = false;
            } else {
                if arr.push(set_1(0, e)).is_none() {
                    return Err(FromStrError::NBE(NotBigEnough(PhantomData)));
                }

                b = true;
            }
        }

        Ok(arr)
    }
}

impl<const N: usize> TryFrom<u8> for UNArr<N> {
    type Error = NotBigEnough<N>;

    fn try_from(x: u8) -> Result<Self, Self::Error> {
        x.to_string().parse().map_err(|e| match e {
            FromStrError::NBE(x) => x,
            FromStrError::ParseInt(_) => unsafe { unreachable_unchecked() },
        })
    }
}

impl<const N: usize> TryFrom<u16> for UNArr<N> {
    type Error = NotBigEnough<N>;

    fn try_from(x: u16) -> Result<Self, Self::Error> {
        x.to_string().parse().map_err(|e| match e {
            FromStrError::NBE(x) => x,
            FromStrError::ParseInt(_) => unsafe { unreachable_unchecked() },
        })
    }
}

impl<const N: usize> TryFrom<u32> for UNArr<N> {
    type Error = NotBigEnough<N>;

    fn try_from(x: u32) -> Result<Self, Self::Error> {
        x.to_string().parse().map_err(|e| match e {
            FromStrError::NBE(x) => x,
            FromStrError::ParseInt(_) => unsafe { unreachable_unchecked() },
        })
    }
}

impl<const N: usize> TryFrom<u64> for UNArr<N> {
    type Error = NotBigEnough<N>;

    fn try_from(x: u64) -> Result<Self, Self::Error> {
        x.to_string().parse().map_err(|e| match e {
            FromStrError::NBE(x) => x,
            FromStrError::ParseInt(_) => unsafe { unreachable_unchecked() },
        })
    }
}

impl<const N: usize> TryFrom<u128> for UNArr<N> {
    type Error = NotBigEnough<N>;

    fn try_from(x: u128) -> Result<Self, Self::Error> {
        x.to_string().parse().map_err(|e| match e {
            FromStrError::NBE(x) => x,
            FromStrError::ParseInt(_) => unsafe { unreachable_unchecked() },
        })
    }
}


const X_MASK: u8 = 0b00001111;
const Y_MASK: u8 = 0b11110000;

fn get_1(x: u8) -> u8 {
    x & X_MASK
}

fn get_2(x: u8) -> u8 {
    x.rotate_right(4) & X_MASK
}

const fn set_1(result: u8, replacement: u8) -> u8 {
    (result & Y_MASK) | replacement
}

const fn set_2(result: u8, replacement: u8) -> u8 {
    (result & X_MASK) | replacement.rotate_right(4)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let mut a = 0b00100001;        

        assert_eq!(get_1(a), 1);
        assert_eq!(get_2(a), 2);

        a = set_1(a, 10);       
        a = set_2(a, 8);
 
        assert_eq!(get_1(a), 10);

        assert_eq!(get_2(a), 8);
    }

    #[test]
    fn add() {
        let mut a = UN::new();

        a += <UNArr<3>>::try_from(10u8).unwrap();
        a += <UNArr<3>>::try_from(10u8).unwrap();

        assert_eq!(a.to_string(), "20");
        a += <UNArr<3>>::try_from(80u8).unwrap();

        assert_eq!(a.to_string(), "100");
    }

    #[test]
    fn mul() {
        assert_eq!(UN::from(2u8) * UN::from(4u8), UN::from(8u8));
    }

    #[test]
    fn iter() {
        let a = UN::from(100u8);

        assert_eq!(a.iter().collect::<Vec<u8>>(), [1, 0, 0])        
    }

    #[test]
    fn order() {
        let a = UN::from(100u8);

        assert!(a > UN::from(10u8));
        assert!(a < UN::from(101u8));
        assert!(a < UN::from(1000u16));

        assert_eq!(a, UN::from(100u8));
    }

}
