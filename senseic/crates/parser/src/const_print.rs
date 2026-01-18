const fn const_slice_end<T>(s: &mut [T], end: usize) -> &mut [T] {
    assert!(end <= s.len());
    unsafe { core::slice::from_raw_parts_mut(s.as_mut_ptr(), end) }
}

pub const fn num_to_str(buf: &mut [u8], x: u16) -> &str {
    if x < 10 {
        buf[0] = (x % 10) as u8 + b'0';
        unsafe { str::from_utf8_unchecked(const_slice_end(buf, 1)) }
    } else if x < 100 {
        buf[0] = (x / 10) as u8 + b'0';
        buf[1] = (x % 10) as u8 + b'0';
        unsafe { str::from_utf8_unchecked(const_slice_end(buf, 2)) }
    } else if x < 1000 {
        buf[0] = (x / 100) as u8 + b'0';
        buf[1] = ((x / 10) % 10) as u8 + b'0';
        buf[2] = (x % 10) as u8 + b'0';
        unsafe { str::from_utf8_unchecked(const_slice_end(buf, 3)) }
    } else {
        todo!()
    }
}

pub const fn const_assert_eq(x: usize, y: usize) {
    if x == y {
        return;
    }
    let mut xbuf = [0u8; 5];
    assert!(x <= u16::MAX as usize, "not equal and left hand side not u16");
    let xs = num_to_str(&mut xbuf, x as u16);
    panic!("{}", xs);
}
