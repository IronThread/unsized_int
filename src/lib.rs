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

/// An unsigned number with a dynamic capacity encoded in base 10 and two digits per byte.
// todo: examples
#[derive(Clone, Hash)]
pub struct UN {
    vec: Vec<u8>
}

impl<T: AsRef<SliceUN>> PartialEq<T> for UN {
    fn eq(&self, other: &T) -> bool {
        self.as_ref() == other.as_ref()
    } 
}

impl Eq for UN {}

impl<T: AsRef<SliceUN>> PartialOrd<T> for UN {
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        self.as_ref().partial_cmp(other.as_ref())
    }
}

impl Ord for UN {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_ref().cmp(other.as_ref())
    }
}

impl UN {
    /// Creates a new `UN` with an empty inner vector,this is the `0` value.
    pub const fn new() -> Self {
        Self {
            vec: Vec::new()
        }
    }

    /// Substracts to `self` value in `other`. If the substraction is less than zero then `self`
    /// becomes zero.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use unsized_int::UN;
    /// 
    /// let mut a = UN::from(6u8);
    /// 
    /// let x = UN::from(3u8);
    /// a.saturating_sub(&x);
    /// 
    /// assert_eq!(a, x);
    /// 
    /// let mut a = UN::from(10u8);
    /// 
    /// let x = UN::from(9u8);
    /// a.saturating_sub(&x);
    /// 
    /// assert_eq!(a, UN::from(1u8)); 
    /// 
    /// let mut a = UN::from(1000u16);
    /// 
    /// let x = UN::from(999u16);
    /// a.saturating_sub(&x);
    /// 
    /// assert_eq!(a, UN::from(1u8));
    /// 
    /// a.saturating_sub(&x);
    /// 
    /// assert_eq!(a, UN::from(0u8));
    /// ``` 
    pub fn saturating_sub<T: AsRef<SliceUN>>(&mut self, other: T) {
        if other.as_ref() > self {
            self.vec.clear();
            return
        }

        let mut b = true;
        let mut it1 = self.vec.iter_mut();

        let mut it2 = other.as_ref().vec.iter().copied();

        let mut e = if let Some(e3) = it1.next() {
            e3
        } else {
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
                let mut x = get_1(*e);
    
                if x < rest {
                    x = 10 - rest;
                    rest = 1;
                } else {
                    x -= rest;
                    rest = 0;
                }
                
                let y = get_1(e2);

                if y > x {
                    rest = 1;
                    *e = set_1(*e, 10 - y);                    
                } else {
                    *e = set_1(*e, x - y);
                }

                b = false;
            } else {
                let mut x = get_2(*e);
                if x < rest {
                    x = 10 - rest;
                    rest = 1;
                } else {
                    x -= rest;
                    rest = 0;
                }
                let y = get_2(e2);

                if y > x {
                    rest = 1;
                    *e = set_2(*e, 10 - y);                    
                } else {
                    *e = set_2(*e, x - y);
                }


                if let Some(e3) = it2.next() {
                    e2 = e3;
                } else {
                    break
                }

                e = it1.next().unwrap();

                b = true;
            }
        }


        let mut i = self.vec.len();

        while i > 0 {
            i -= 1;

            if self.vec[i] == 0 {
                self.vec.pop();
            } else {
                break
            }
        }
    }
}

impl AsRef<SliceUN> for UN {
    #[inline]
    fn as_ref(&self) -> &SliceUN {
        self.deref()
    }
}

impl AsMut<SliceUN> for UN {
    #[inline]
    fn as_mut(&mut self) -> &mut SliceUN {
        self.deref_mut()
    }
}

impl Borrow<SliceUN> for UN {
    #[inline]
    fn borrow(&self) -> &SliceUN {
        self.deref()
    }
}

impl BorrowMut<SliceUN> for UN {
    #[inline]
    fn borrow_mut(&mut self) -> &mut SliceUN {
        self.deref_mut()
    }
}

impl<T: AsRef<SliceUN>> Add<T> for UN {
    type Output = Self;

    #[inline]
    fn add(mut self, other: T) -> Self::Output {
        self += other;
        self
    }
}

impl<T: AsRef<SliceUN>> AddAssign<T> for UN {
    fn add_assign(&mut self, other: T) {
        let mut b = true;

        let a: &mut UN = unsafe { &mut *(self as *mut _) };
        let len = self.vec.len();
        let mut it1 = self.vec.iter_mut();

        let mut it2len = other.as_ref().vec.len();
        let mut it2 = other.as_ref().vec.iter().copied();

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
                        e2 = 0;
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

impl<T: AsRef<SliceUN>> Mul<T> for UN {
    type Output = Self;

    #[inline]
    fn mul(mut self, other: T) -> Self::Output {
        self *= other;
        self
    }
}

impl<T: AsRef<SliceUN>> MulAssign<T> for UN {
    fn mul_assign(&mut self, other: T) {
        let mut b = true;

        let a: &mut UN = unsafe { &mut *(self as *mut _) };
        let len = self.vec.len();
        let mut it1 = self.vec.iter_mut();

        let mut it2len = other.as_ref().vec.len();
        let mut it2 = other.as_ref().vec.iter().copied();

        let mut e = if let Some(e3) = it1.next() {
            e3
        } else {
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
                        e2 = 0;
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
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self.deref(), f)
    }
}

impl Debug for UN  {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self.deref(), f)
    }
}

impl Deref for UN {
    type Target = SliceUN;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { &*(&*self.vec as *const _ as *const SliceUN) }
    }
}

impl DerefMut for UN {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *(&mut *self.vec as *mut _ as *mut SliceUN) }
    }
}

impl FromStr for UN {
    type Err = ParseIntError;

    fn from_str(x: &str) -> Result<Self, Self::Err> {
        if x.is_empty() {
            let _: u8 = "".parse()?;
        }

        let mut a = UN::new();

        let mut b = false;

        let mut last = 0;

        let mut it = x.chars();

        while let Some(c) = it.next() {
            let e = c.to_string().parse::<u8>()?;

            if e != 0 {
                last = e;
                break
            }
        }        

        for c in it.rev() {
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


        if last != 0 {
            if b {
                let x = a.vec.last_mut().unwrap();

                *x = set_2(*x, last);
            } else {
                a.vec.push(set_1(0, last));
            }
        }

        Ok(a)
    }
}

impl From<u8> for UN {
    #[inline]
    fn from(x: u8) -> Self {
        x.to_string().parse().unwrap()
    }
}

impl From<u16> for UN {
    #[inline]
    fn from(x: u16) -> Self {
        x.to_string().parse().unwrap()
    }
}

impl From<u32> for UN {
    #[inline]
    fn from(x: u32) -> Self {
        x.to_string().parse().unwrap()
    }
}

impl From<u64> for UN {
    #[inline]
    fn from(x: u64) -> Self {
        x.to_string().parse().unwrap()
    }
}

impl From<u128> for UN {
    #[inline]
    fn from(x: u128) -> Self {
        x.to_string().parse().unwrap()
    }
}

#[derive(PartialEq, Eq, Hash)]
pub struct SliceUN {
    vec: [u8]
}

impl SliceUN {
    /// Creates an iterator that yields all the base 10 digits of this number.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use unsized_int::UN;
    /// 
    /// let a = UN::from(100u8);
    /// 
    /// assert_eq!(a.iter().collect::<Vec<u8>>(), [1, 0, 0]);
    /// ```
    pub fn iter(&self) -> UNIter<'_> {            

        if self.vec.len() > 0 {
            let a = *self.vec.last().unwrap();

            let x = get_2(a);
            let get_2 = x > 0;
            UNIter {
                slice: self,
                index: self.vec.len() - 1,
                len: if get_2 {
                    self.vec.len() * 2
                } else {
                    (self.vec.len() * 2) - 1
                },
                get_2,
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

    pub fn ajust(&self, rep: &str) -> String {
        use std::fmt::Write;

        let mut it = self.iter();
        let mut result = String::new();

        if it.len() > 3 {
            let mut point = false;
            let mut point_count = 0;

            if (it.len() - 1) % 3 == 0 {
                point = true;
            } else if (it.len() - 2) % 3 == 0 {
                point_count = 1;
            }   
            
            while let Some(c) = it.next() { 
                write!(result, "{}", c).unwrap();
        
                if point && it.len() != 0 {
                    result.push_str(rep);
                    point = false;
                    point_count = 0;
                } else {
                    point_count += 1;
        
                    if point_count == 2 {
                        point = true;
                    }
                }                                    
            }        
        } else {
            for e in it {
                write!(result, "{}", e).unwrap();
            }
        }

        result
    }
}

/// Struct created by [`SliceUN::iter`].
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

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a> ExactSizeIterator for UNIter<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.len
    }
}

impl AsRef<SliceUN> for SliceUN {
    #[inline]
    fn as_ref(&self) -> &Self {
        self
    }
}

impl AsMut<SliceUN> for SliceUN {
    #[inline]
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

impl PartialOrd for SliceUN {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SliceUN {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        let it1 = self.iter();
        let it2 = other.iter();

        if it1.len() < it2.len() {
            Ordering::Less
        } else if it1.len() > it2.len() {
            Ordering::Greater
        } else {
            it1.cmp(it2)
        }
    }
}

impl Display for SliceUN  {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {

        let it = self.iter();

        if it.len() == 0 {
            write!(f, "0")?;
        } else {
            for e in it {
                write!(f, "{}", e)?;
            }
        }

        Ok(())
    }
}

impl Debug for SliceUN  {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[derive(Clone, Copy)]
pub struct UNArr<const N: usize> {
    vec: [MaybeUninit<u8>; N],
    len: usize,
}

impl<const N: usize, T: AsRef<SliceUN>> PartialEq<T> for UNArr<N> {
    fn eq(&self, other: &T) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl<const N: usize> Eq for UNArr<N> {}

impl<const N: usize, T: AsRef<SliceUN>> PartialOrd<T> for UNArr<N> {
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        self.as_ref().partial_cmp(other.as_ref())
    }
}

impl<const N: usize> Ord for UNArr<N> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_ref().cmp(other.as_ref())
    }
}

impl<const N: usize> UNArr<N> {
    pub const MIN: Self = Self::new();
    pub const MAX: Self = Self {
        vec: [MaybeUninit::new(set_2(set_1(0, 9), 9)); N],
        len: N
    };

    pub const fn new() -> Self {
        Self {
            vec: [MaybeUninit::uninit(); N],
            len: 0,
        }
    }

    fn push(&mut self, x: u8) -> Option<()> {
        self.vec.get_mut(self.len)?.write(x);
        self.len += 1;
        Some(())
    }

    fn pop(&mut self) -> Option<u8> {
        let new_len = self.len.checked_sub(1)?;
        let x = self.get_slice()[new_len];
        self.len = new_len;
        Some(x)
    }

    fn get_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.vec.as_ptr().cast(), self.len) }
    }

    fn get_slice_mut(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.vec.as_mut_ptr().cast(), self.len) }
    }

    pub fn wrapping_sub<const N2: usize>(&mut self, other: UNArr<N2>) {
        if other.as_ref() > self {
            let mut d = other;

            d.wrapping_sub(*self);

            *self = Self::MAX;
            self.wrapping_sub(d);
            return
        }

        let mut b = true;

        let mut it1 = self.get_slice_mut().iter_mut();

        let mut it2 = other.get_slice().iter().copied();

        let mut e2 = if let Some(e3) = it2.next() {
            e3
        } else {
            return
        };

        let mut e = if let Some(e3) = it1.next() {
            e3
        } else {
            *self = Self::MAX;
            self.wrapping_sub(other);
            return
        };
        
        let mut rest = 0;

        loop {
            if b {
                let mut x = get_1(*e);
    
                if x < rest {
                    x = 10 - rest;
                    rest = 1;
                } else {
                    x -= rest;
                    rest = 0;
                }
                
                let y = get_1(e2);

                if y > x {
                    rest = 1;
                    *e = set_1(*e, 10 - y);                    
                } else {
                    *e = set_1(*e, x - y);
                }

                b = false;
            } else {
                let mut x = get_2(*e);
                if x < rest {
                    x = 10 - rest;
                    rest = 1;
                } else {
                    x -= rest;
                    rest = 0;
                }
                let y = get_2(e2);

                if y > x {
                    rest = 1;
                    *e = set_2(*e, 10 - y);                    
                } else {
                    *e = set_2(*e, x - y);
                }


                if let Some(e3) = it2.next() {
                    e2 = e3;
                } else {
                    break
                }

                e = it1.next().unwrap();

                b = true;
            }
        }


        let mut i = self.get_slice().len();

        while i > 0 {
            i -= 1;

            if self.get_slice()[i] == 0 {
                self.pop();
            } else {
                break
            }
        }        
    }
}

impl<const N: usize> AsRef<SliceUN> for  UNArr<N> {
    fn as_ref(&self) -> &SliceUN {
        self.deref()
    }
}

impl<const N: usize> AsMut<SliceUN> for  UNArr<N> {
    fn as_mut(&mut self) -> &mut SliceUN {
        self.deref_mut()
    }
}

impl<const N: usize> Borrow<SliceUN> for  UNArr<N> {
    fn borrow(&self) -> &SliceUN {
        self.deref()
    }
}

impl<const N: usize> BorrowMut<SliceUN> for  UNArr<N> {
    fn borrow_mut(&mut self) -> &mut SliceUN {
        self.deref_mut()
    }
}

impl<const N: usize> Deref for UNArr<N> {
    type Target = SliceUN;

    fn deref(&self) -> &Self::Target {
        unsafe { &*(self.get_slice() as *const [u8] as *const SliceUN) }
    }
}

impl<const N: usize> DerefMut for UNArr<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *(self.get_slice_mut() as *mut [u8] as *mut SliceUN) }
    }
}


impl<const N: usize> Display for UNArr<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self.as_ref(), f)
    }
}

impl<const N: usize> Debug for UNArr<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
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
        if x.is_empty() {
            let _: u8 = "".parse().map_err(FromStrError::ParseInt)?;
        }

        let mut arr = UNArr::new();

        let mut b = false;        

        let mut last = 0;

        let mut it = x.chars();

        while let Some(c) = it.next() {
            let e = c.to_string().parse::<u8>().map_err(FromStrError::ParseInt)?;

            if e != 0 {
                last = e;
                break
            }
        }        

        for c in it.rev() {
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


        if last != 0 {
            if b {
                let x = arr.get_slice_mut().last_mut().unwrap();

                *x = set_2(*x, last);
            } else {
                if arr.push(set_1(0, last)).is_none() {
                    return Err(FromStrError::NBE(NotBigEnough(PhantomData)));
                }
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

const fn get_1(x: u8) -> u8 {
    x & X_MASK
}

const fn get_2(x: u8) -> u8 {
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
    // todo: this was all tested on a little endian machine,i dunno if it works correctly on a  big
    // endian one
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
    fn order() {
        let a = UN::from(100u8);

        assert!(a > UN::from(10u8));
        assert!(a < UN::from(101u8));
        assert!(a < UN::from(1000u16));

        assert_eq!(a, UN::from(100u8));
    }

    #[test]
    fn ajust() {
        let a = <UNArr<2>>::try_from(1000u16).unwrap();

        assert_eq!(a.ajust("."), "1.000");

        let a = <UNArr<3>>::try_from(10000u16).unwrap();

        assert_eq!(a.ajust("."), "10.000");

        let a = <UNArr<3>>::try_from(100000u32).unwrap();

        assert_eq!(a.ajust("."), "100.000");        

        let a = <UNArr<4>>::try_from(1000000u32).unwrap();

        assert_eq!(a.ajust("."), "1.000.000")
    }

    #[test]
    fn wrapping_sub() {
        
        let mut a = <UNArr<3>>::try_from(6u8).unwrap();
         
        let x = <UNArr<3>>::try_from(3u8).unwrap();
        a.wrapping_sub(x);
        
        assert_eq!(a, x);
        
        let mut a = <UNArr<3>>::try_from(10u8).unwrap();
        
        let x = <UNArr<3>>::try_from(9u8).unwrap();
        a.wrapping_sub(x);
        
        assert_eq!(a, UN::from(1u8)); 
        
        let mut a = <UNArr<3>>::try_from(1000u16).unwrap();
        
        let x = <UNArr<3>>::try_from(999u16).unwrap();
        a.wrapping_sub(x);
        
        assert_eq!(a, UN::from(1u8));
        
        a.wrapping_sub(x);
         
        assert_eq!(UN::from(999001u32), a);    
    }
}
