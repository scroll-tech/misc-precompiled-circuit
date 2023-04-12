pub const DIGEST_BUF_LEN: usize = 5;
pub const WORK_BUF_LEN: usize = 16;
pub const H0: [u32; DIGEST_BUF_LEN] = [
    0x6745_2301,
    0xefcd_ab89,
    0x98ba_dcfe,
    0x1032_5476,
    0xc3d2_e1f0,
];

pub trait RMD160Atomic{
    fn f(x: Self, y: Self, z: Self) -> Self;
    fn g(x: Self, y: Self, z: Self) -> Self;
    fn h(x: Self, y: Self, z: Self) -> Self;
    fn i(x: Self, y: Self, z: Self) -> Self;
    fn j(x: Self, y: Self, z: Self) -> Self;
    fn atomic(round: usize, x: u32, y:u32, z:u32) -> u32;
}

impl RMD160Atomic for u32 {
    fn f(x: u32, y: u32, z: u32) -> u32 {
        x ^ y ^ z
    }
    fn g(x: u32, y: u32, z: u32) -> u32 {
        (x & y) | ((!x) & z)
    }
    fn h(x: u32, y: u32, z: u32) -> u32 {
        (x | (!y)) ^ z
    }
    fn i(x: u32, y: u32, z: u32) -> u32 {
        (x & z) | (y & (!z))
    }

    fn j(x: u32, y: u32, z: u32) -> u32 {
        x ^ (y | (!z))
    }

    fn atomic(round: usize, x: u32, y:u32, z:u32) -> u32 {
        match round {
            0 => u32::f(x, y, z),
            1 => u32::g(x, y, z),
            2 => u32::h(x, y, z),
            3 => u32::i(x, y, z),
            4 => u32::j(x, y, z),
            _ => unreachable!(),
        }
    }
}


fn rol_modifier(round: usize, rol: &mut Vec<u32>, x: u32, offset: u32, shift: u32) {
    let v = match round {
        0 => u32::f(rol[1], rol[2], rol[3]),
        1 => u32::g(rol[1], rol[2], rol[3]),
        2 => u32::h(rol[1], rol[2], rol[3]),
        3 => u32::i(rol[1], rol[2], rol[3]),
        4 => u32::j(rol[1], rol[2], rol[3]),
        _ => unreachable!(),
    };
    rol[0] = rol[0].wrapping_add(v).wrapping_add(x).wrapping_add(offset);
    rol[0] = rol[0].rotate_left(shift).wrapping_add(rol[4]);
    rol[2] = rol[2].rotate_left(10);
}

pub(crate) const ROUNDS_OFFSET: [u32; DIGEST_BUF_LEN] = [
    0x0, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e,
];

pub(crate) const PROUNDS_OFFSET: [u32; DIGEST_BUF_LEN] = [
    0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x0
];

/*round1*/
pub(crate) const R: [[u32; 16]; DIGEST_BUF_LEN] = [
    [11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8],
    [7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12],
    [11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5],
    [11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12],
    [9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6],
];

pub(crate) const O: [[usize; 16]; DIGEST_BUF_LEN] = [
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
    [7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8],
    [3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12],
    [1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2],
    [4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13],
];

/*parallelround1*/
pub(crate) const PR: [[u32; 16]; DIGEST_BUF_LEN] = [
    [8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6],
    [9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11],
    [9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5],
    [15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8],
    [8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11],
];

pub(crate) const PO: [[usize; 16]; DIGEST_BUF_LEN] = [
    [5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12],
    [6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2],
    [15,5,1,3,7,14,6,9,11,8,12,2,10,0,4,13],
    [8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14],
    [12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11],
];

pub fn compress(w: &Vec<u32>, values: Vec<u32>) -> Vec<u32> {
    let mut rol1 = w.clone();
    let mut rol2 = w.clone();
    let mut round = 0;
    for ((idxs,shift), offset) in O.zip(R).zip(ROUNDS_OFFSET) {
        for limb_index in 0..16 {
            let idx = idxs[limb_index];
            rol_modifier(round, &mut rol1, values[idx], offset, shift[limb_index]);
            rol1.rotate_right(1);
            println!("{:?}", rol1);
        }
        round += 1;
    }

    for ((idxs,shift), offset) in PO.zip(PR).zip(PROUNDS_OFFSET) {
        for limb_index in 0..16 {
            let idx = idxs[limb_index];
            rol_modifier(round-1, &mut rol2, values[idx], offset, shift[limb_index]);
            rol2.rotate_right(1);
            println!("{:?}, shift {} x {} offset {}", rol2, shift[limb_index], values[idx], offset);
        }
        round -= 1;
    }

    let mut r = vec![];
    let len = w.len();
    for i in 0..w.len() {
        r.push(w[i].wrapping_add(rol1[(i+1)%len]).wrapping_add(rol2[(i+2)%len]));
    }
    r.rotate_left(1);
    r
}

#[cfg(test)]
mod tests {

    macro_rules! round(
        ($a:expr, $b:expr, $c:expr, $d:expr, $e:expr,
         $x:expr, $bits:expr, $add:expr, $round:expr) => ({
            $a = $a.wrapping_add($round).wrapping_add($x).wrapping_add($add);
            $a = $a.rotate_left($bits).wrapping_add($e);
            $c = $c.rotate_left(10);
        });
    );

    macro_rules! process_block(
        ($h:ident, $data:expr,
         $( round1: h_ordering $f0:expr, $f1:expr, $f2:expr, $f3:expr, $f4:expr;
                    data_index $data_index1:expr; roll_shift $bits1:expr )*;
         $( round2: h_ordering $g0:expr, $g1:expr, $g2:expr, $g3:expr, $g4:expr;
                    data_index $data_index2:expr; roll_shift $bits2:expr )*;
         $( round3: h_ordering $h0:expr, $h1:expr, $h2:expr, $h3:expr, $h4:expr;
                    data_index $data_index3:expr; roll_shift $bits3:expr )*;
         $( round4: h_ordering $i0:expr, $i1:expr, $i2:expr, $i3:expr, $i4:expr;
                    data_index $data_index4:expr; roll_shift $bits4:expr )*;
         $( round5: h_ordering $j0:expr, $j1:expr, $j2:expr, $j3:expr, $j4:expr;
                    data_index $data_index5:expr; roll_shift $bits5:expr )*;
         $( par_round1: h_ordering $pj0:expr, $pj1:expr, $pj2:expr, $pj3:expr, $pj4:expr;
                        data_index $pdata_index1:expr; roll_shift $pbits1:expr )*;
         $( par_round2: h_ordering $pi0:expr, $pi1:expr, $pi2:expr, $pi3:expr, $pi4:expr;
                        data_index $pdata_index2:expr; roll_shift $pbits2:expr )*;
         $( par_round3: h_ordering $ph0:expr, $ph1:expr, $ph2:expr, $ph3:expr, $ph4:expr;
                        data_index $pdata_index3:expr; roll_shift $pbits3:expr )*;
         $( par_round4: h_ordering $pg0:expr, $pg1:expr, $pg2:expr, $pg3:expr, $pg4:expr;
                        data_index $pdata_index4:expr; roll_shift $pbits4:expr )*;
         $( par_round5: h_ordering $pf0:expr, $pf1:expr, $pf2:expr, $pf3:expr, $pf4:expr;
                        data_index $pdata_index5:expr; roll_shift $pbits5:expr )*;
        ) => ({
            let mut bb = *$h;
            let mut bbb = *$h;

            // Round 1
            $( round!(bb[$f0], bb[$f1], bb[$f2], bb[$f3], bb[$f4],
                      $data[$data_index1], $bits1, 0x0000_0000,
                      bb[$f1] ^ bb[$f2] ^ bb[$f3]); )*

            // Round 2
            $( round!(bb[$g0], bb[$g1], bb[$g2], bb[$g3], bb[$g4],
                      $data[$data_index2], $bits2, 0x5a82_7999,
                      (bb[$g1] & bb[$g2]) | (!bb[$g1] & bb[$g3])); )*

            // Round 3
            $( round!(bb[$h0], bb[$h1], bb[$h2], bb[$h3], bb[$h4],
                      $data[$data_index3], $bits3, 0x6ed9_eba1,
                      (bb[$h1] | !bb[$h2]) ^ bb[$h3]); )*

            // Round 4
            $( round!(bb[$i0], bb[$i1], bb[$i2], bb[$i3], bb[$i4],
                      $data[$data_index4], $bits4, 0x8f1b_bcdc,
                      (bb[$i1] & bb[$i3]) | (bb[$i2] & !bb[$i3])); )*

            // Round 5
            $( round!(bb[$j0], bb[$j1], bb[$j2], bb[$j3], bb[$j4],
                      $data[$data_index5], $bits5, 0xa953_fd4e,
                      bb[$j1] ^ (bb[$j2] | !bb[$j3])); )*

            // Parallel rounds: these are the same as the previous five
            // rounds except that the constants have changed, we work
            // with the other buffer, and they are applied in reverse
            // order.

            // Parallel Round 1
            $( round!(bbb[$pj0], bbb[$pj1], bbb[$pj2], bbb[$pj3], bbb[$pj4],
                      $data[$pdata_index1], $pbits1, 0x50a2_8be6,
                      bbb[$pj1] ^ (bbb[$pj2] | !bbb[$pj3])); )*

            // Parallel Round 2
            $( round!(bbb[$pi0], bbb[$pi1], bbb[$pi2], bbb[$pi3], bbb[$pi4],
                      $data[$pdata_index2], $pbits2, 0x5c4d_d124,
                      (bbb[$pi1] & bbb[$pi3]) | (bbb[$pi2] & !bbb[$pi3])); )*

            // Parallel Round 3
            $( round!(bbb[$ph0], bbb[$ph1], bbb[$ph2], bbb[$ph3], bbb[$ph4],
                      $data[$pdata_index3], $pbits3, 0x6d70_3ef3,
                      (bbb[$ph1] | !bbb[$ph2]) ^ bbb[$ph3]); )*

            // Parallel Round 4
            $( round!(bbb[$pg0], bbb[$pg1], bbb[$pg2], bbb[$pg3], bbb[$pg4],
                      $data[$pdata_index4], $pbits4, 0x7a6d_76e9,
                      (bbb[$pg1] & bbb[$pg2]) | (!bbb[$pg1] & bbb[$pg3])); )*

            // Parallel Round 5
            $( round!(bbb[$pf0], bbb[$pf1], bbb[$pf2], bbb[$pf3], bbb[$pf4],
                      $data[$pdata_index5], $pbits5, 0x0000_0000,
                      bbb[$pf1] ^ bbb[$pf2] ^ bbb[$pf3]); )*

            // Combine results
            bbb[3] = bbb[3].wrapping_add($h[1]).wrapping_add(bb[2]);
            $h[1]   = $h[2].wrapping_add(bb[3]).wrapping_add(bbb[4]);
            $h[2]   = $h[3].wrapping_add(bb[4]).wrapping_add(bbb[0]);
            $h[3]   = $h[4].wrapping_add(bb[0]).wrapping_add(bbb[1]);
            $h[4]   = $h[0].wrapping_add(bb[1]).wrapping_add(bbb[2]);
            $h[0]   =                 bbb[3];
        });
    );

    pub fn compress(h: &mut [u32; super::DIGEST_BUF_LEN], data: &[u8; 64]) {
        let mut w = [0u32; super::WORK_BUF_LEN];
        for (o, chunk) in w.iter_mut().zip(data.chunks_exact(4)) {
            *o = u32::from_le_bytes(chunk.try_into().unwrap());
        }
        process_block!(h, w[..],
        // Round 1
            round1: h_ordering 0, 1, 2, 3, 4; data_index  0; roll_shift 11
            round1: h_ordering 4, 0, 1, 2, 3; data_index  1; roll_shift 14
            round1: h_ordering 3, 4, 0, 1, 2; data_index  2; roll_shift 15
            round1: h_ordering 2, 3, 4, 0, 1; data_index  3; roll_shift 12
            round1: h_ordering 1, 2, 3, 4, 0; data_index  4; roll_shift  5
            round1: h_ordering 0, 1, 2, 3, 4; data_index  5; roll_shift  8
            round1: h_ordering 4, 0, 1, 2, 3; data_index  6; roll_shift  7
            round1: h_ordering 3, 4, 0, 1, 2; data_index  7; roll_shift  9
            round1: h_ordering 2, 3, 4, 0, 1; data_index  8; roll_shift 11
            round1: h_ordering 1, 2, 3, 4, 0; data_index  9; roll_shift 13
            round1: h_ordering 0, 1, 2, 3, 4; data_index 10; roll_shift 14
            round1: h_ordering 4, 0, 1, 2, 3; data_index 11; roll_shift 15
            round1: h_ordering 3, 4, 0, 1, 2; data_index 12; roll_shift  6
            round1: h_ordering 2, 3, 4, 0, 1; data_index 13; roll_shift  7
            round1: h_ordering 1, 2, 3, 4, 0; data_index 14; roll_shift  9
            round1: h_ordering 0, 1, 2, 3, 4; data_index 15; roll_shift  8;

        // Round 2
            round2: h_ordering 4, 0, 1, 2, 3; data_index  7; roll_shift  7
            round2: h_ordering 3, 4, 0, 1, 2; data_index  4; roll_shift  6
            round2: h_ordering 2, 3, 4, 0, 1; data_index 13; roll_shift  8
            round2: h_ordering 1, 2, 3, 4, 0; data_index  1; roll_shift 13
            round2: h_ordering 0, 1, 2, 3, 4; data_index 10; roll_shift 11
            round2: h_ordering 4, 0, 1, 2, 3; data_index  6; roll_shift  9
            round2: h_ordering 3, 4, 0, 1, 2; data_index 15; roll_shift  7
            round2: h_ordering 2, 3, 4, 0, 1; data_index  3; roll_shift 15
            round2: h_ordering 1, 2, 3, 4, 0; data_index 12; roll_shift  7
            round2: h_ordering 0, 1, 2, 3, 4; data_index  0; roll_shift 12
            round2: h_ordering 4, 0, 1, 2, 3; data_index  9; roll_shift 15
            round2: h_ordering 3, 4, 0, 1, 2; data_index  5; roll_shift  9
            round2: h_ordering 2, 3, 4, 0, 1; data_index  2; roll_shift 11
            round2: h_ordering 1, 2, 3, 4, 0; data_index 14; roll_shift  7
            round2: h_ordering 0, 1, 2, 3, 4; data_index 11; roll_shift 13
            round2: h_ordering 4, 0, 1, 2, 3; data_index  8; roll_shift 12;

        // Round 3
            round3: h_ordering 3, 4, 0, 1, 2; data_index  3; roll_shift 11
            round3: h_ordering 2, 3, 4, 0, 1; data_index 10; roll_shift 13
            round3: h_ordering 1, 2, 3, 4, 0; data_index 14; roll_shift  6
            round3: h_ordering 0, 1, 2, 3, 4; data_index  4; roll_shift  7
            round3: h_ordering 4, 0, 1, 2, 3; data_index  9; roll_shift 14
            round3: h_ordering 3, 4, 0, 1, 2; data_index 15; roll_shift  9
            round3: h_ordering 2, 3, 4, 0, 1; data_index  8; roll_shift 13
            round3: h_ordering 1, 2, 3, 4, 0; data_index  1; roll_shift 15
            round3: h_ordering 0, 1, 2, 3, 4; data_index  2; roll_shift 14
            round3: h_ordering 4, 0, 1, 2, 3; data_index  7; roll_shift  8
            round3: h_ordering 3, 4, 0, 1, 2; data_index  0; roll_shift 13
            round3: h_ordering 2, 3, 4, 0, 1; data_index  6; roll_shift  6
            round3: h_ordering 1, 2, 3, 4, 0; data_index 13; roll_shift  5
            round3: h_ordering 0, 1, 2, 3, 4; data_index 11; roll_shift 12
            round3: h_ordering 4, 0, 1, 2, 3; data_index  5; roll_shift  7
            round3: h_ordering 3, 4, 0, 1, 2; data_index 12; roll_shift  5;

        // Round 4
            round4: h_ordering 2, 3, 4, 0, 1; data_index  1; roll_shift 11
            round4: h_ordering 1, 2, 3, 4, 0; data_index  9; roll_shift 12
            round4: h_ordering 0, 1, 2, 3, 4; data_index 11; roll_shift 14
            round4: h_ordering 4, 0, 1, 2, 3; data_index 10; roll_shift 15
            round4: h_ordering 3, 4, 0, 1, 2; data_index  0; roll_shift 14
            round4: h_ordering 2, 3, 4, 0, 1; data_index  8; roll_shift 15
            round4: h_ordering 1, 2, 3, 4, 0; data_index 12; roll_shift  9
            round4: h_ordering 0, 1, 2, 3, 4; data_index  4; roll_shift  8
            round4: h_ordering 4, 0, 1, 2, 3; data_index 13; roll_shift  9
            round4: h_ordering 3, 4, 0, 1, 2; data_index  3; roll_shift 14
            round4: h_ordering 2, 3, 4, 0, 1; data_index  7; roll_shift  5
            round4: h_ordering 1, 2, 3, 4, 0; data_index 15; roll_shift  6
            round4: h_ordering 0, 1, 2, 3, 4; data_index 14; roll_shift  8
            round4: h_ordering 4, 0, 1, 2, 3; data_index  5; roll_shift  6
            round4: h_ordering 3, 4, 0, 1, 2; data_index  6; roll_shift  5
            round4: h_ordering 2, 3, 4, 0, 1; data_index  2; roll_shift 12;

        // Round 5
            round5: h_ordering 1, 2, 3, 4, 0; data_index  4; roll_shift  9
            round5: h_ordering 0, 1, 2, 3, 4; data_index  0; roll_shift 15
            round5: h_ordering 4, 0, 1, 2, 3; data_index  5; roll_shift  5
            round5: h_ordering 3, 4, 0, 1, 2; data_index  9; roll_shift 11
            round5: h_ordering 2, 3, 4, 0, 1; data_index  7; roll_shift  6
            round5: h_ordering 1, 2, 3, 4, 0; data_index 12; roll_shift  8
            round5: h_ordering 0, 1, 2, 3, 4; data_index  2; roll_shift 13
            round5: h_ordering 4, 0, 1, 2, 3; data_index 10; roll_shift 12
            round5: h_ordering 3, 4, 0, 1, 2; data_index 14; roll_shift  5
            round5: h_ordering 2, 3, 4, 0, 1; data_index  1; roll_shift 12
            round5: h_ordering 1, 2, 3, 4, 0; data_index  3; roll_shift 13
            round5: h_ordering 0, 1, 2, 3, 4; data_index  8; roll_shift 14
            round5: h_ordering 4, 0, 1, 2, 3; data_index 11; roll_shift 11
            round5: h_ordering 3, 4, 0, 1, 2; data_index  6; roll_shift  8
            round5: h_ordering 2, 3, 4, 0, 1; data_index 15; roll_shift  5
            round5: h_ordering 1, 2, 3, 4, 0; data_index 13; roll_shift  6;

        // Parallel Round 1
            par_round1: h_ordering 0, 1, 2, 3, 4; data_index  5; roll_shift  8
            par_round1: h_ordering 4, 0, 1, 2, 3; data_index 14; roll_shift  9
            par_round1: h_ordering 3, 4, 0, 1, 2; data_index  7; roll_shift  9
            par_round1: h_ordering 2, 3, 4, 0, 1; data_index  0; roll_shift 11
            par_round1: h_ordering 1, 2, 3, 4, 0; data_index  9; roll_shift 13
            par_round1: h_ordering 0, 1, 2, 3, 4; data_index  2; roll_shift 15
            par_round1: h_ordering 4, 0, 1, 2, 3; data_index 11; roll_shift 15
            par_round1: h_ordering 3, 4, 0, 1, 2; data_index  4; roll_shift  5
            par_round1: h_ordering 2, 3, 4, 0, 1; data_index 13; roll_shift  7
            par_round1: h_ordering 1, 2, 3, 4, 0; data_index  6; roll_shift  7
            par_round1: h_ordering 0, 1, 2, 3, 4; data_index 15; roll_shift  8
            par_round1: h_ordering 4, 0, 1, 2, 3; data_index  8; roll_shift 11
            par_round1: h_ordering 3, 4, 0, 1, 2; data_index  1; roll_shift 14
            par_round1: h_ordering 2, 3, 4, 0, 1; data_index 10; roll_shift 14
            par_round1: h_ordering 1, 2, 3, 4, 0; data_index  3; roll_shift 12
            par_round1: h_ordering 0, 1, 2, 3, 4; data_index 12; roll_shift  6;

        // Parallel Round 2
            par_round2: h_ordering 4, 0, 1, 2, 3; data_index  6; roll_shift  9
            par_round2: h_ordering 3, 4, 0, 1, 2; data_index 11; roll_shift 13
            par_round2: h_ordering 2, 3, 4, 0, 1; data_index  3; roll_shift 15
            par_round2: h_ordering 1, 2, 3, 4, 0; data_index  7; roll_shift  7
            par_round2: h_ordering 0, 1, 2, 3, 4; data_index  0; roll_shift 12
            par_round2: h_ordering 4, 0, 1, 2, 3; data_index 13; roll_shift  8
            par_round2: h_ordering 3, 4, 0, 1, 2; data_index  5; roll_shift  9
            par_round2: h_ordering 2, 3, 4, 0, 1; data_index 10; roll_shift 11
            par_round2: h_ordering 1, 2, 3, 4, 0; data_index 14; roll_shift  7
            par_round2: h_ordering 0, 1, 2, 3, 4; data_index 15; roll_shift  7
            par_round2: h_ordering 4, 0, 1, 2, 3; data_index  8; roll_shift 12
            par_round2: h_ordering 3, 4, 0, 1, 2; data_index 12; roll_shift  7
            par_round2: h_ordering 2, 3, 4, 0, 1; data_index  4; roll_shift  6
            par_round2: h_ordering 1, 2, 3, 4, 0; data_index  9; roll_shift 15
            par_round2: h_ordering 0, 1, 2, 3, 4; data_index  1; roll_shift 13
            par_round2: h_ordering 4, 0, 1, 2, 3; data_index  2; roll_shift 11;

        // Parallel Round 3
            par_round3: h_ordering 3, 4, 0, 1, 2; data_index 15; roll_shift  9
            par_round3: h_ordering 2, 3, 4, 0, 1; data_index  5; roll_shift  7
            par_round3: h_ordering 1, 2, 3, 4, 0; data_index  1; roll_shift 15
            par_round3: h_ordering 0, 1, 2, 3, 4; data_index  3; roll_shift 11
            par_round3: h_ordering 4, 0, 1, 2, 3; data_index  7; roll_shift  8
            par_round3: h_ordering 3, 4, 0, 1, 2; data_index 14; roll_shift  6
            par_round3: h_ordering 2, 3, 4, 0, 1; data_index  6; roll_shift  6
            par_round3: h_ordering 1, 2, 3, 4, 0; data_index  9; roll_shift 14
            par_round3: h_ordering 0, 1, 2, 3, 4; data_index 11; roll_shift 12
            par_round3: h_ordering 4, 0, 1, 2, 3; data_index  8; roll_shift 13
            par_round3: h_ordering 3, 4, 0, 1, 2; data_index 12; roll_shift  5
            par_round3: h_ordering 2, 3, 4, 0, 1; data_index  2; roll_shift 14
            par_round3: h_ordering 1, 2, 3, 4, 0; data_index 10; roll_shift 13
            par_round3: h_ordering 0, 1, 2, 3, 4; data_index  0; roll_shift 13
            par_round3: h_ordering 4, 0, 1, 2, 3; data_index  4; roll_shift  7
            par_round3: h_ordering 3, 4, 0, 1, 2; data_index 13; roll_shift  5;

        // Parallel Round 4
            par_round4: h_ordering 2, 3, 4, 0, 1; data_index  8; roll_shift 15
            par_round4: h_ordering 1, 2, 3, 4, 0; data_index  6; roll_shift  5
            par_round4: h_ordering 0, 1, 2, 3, 4; data_index  4; roll_shift  8
            par_round4: h_ordering 4, 0, 1, 2, 3; data_index  1; roll_shift 11
            par_round4: h_ordering 3, 4, 0, 1, 2; data_index  3; roll_shift 14
            par_round4: h_ordering 2, 3, 4, 0, 1; data_index 11; roll_shift 14
            par_round4: h_ordering 1, 2, 3, 4, 0; data_index 15; roll_shift  6
            par_round4: h_ordering 0, 1, 2, 3, 4; data_index  0; roll_shift 14
            par_round4: h_ordering 4, 0, 1, 2, 3; data_index  5; roll_shift  6
            par_round4: h_ordering 3, 4, 0, 1, 2; data_index 12; roll_shift  9
            par_round4: h_ordering 2, 3, 4, 0, 1; data_index  2; roll_shift 12
            par_round4: h_ordering 1, 2, 3, 4, 0; data_index 13; roll_shift  9
            par_round4: h_ordering 0, 1, 2, 3, 4; data_index  9; roll_shift 12
            par_round4: h_ordering 4, 0, 1, 2, 3; data_index  7; roll_shift  5
            par_round4: h_ordering 3, 4, 0, 1, 2; data_index 10; roll_shift 15
            par_round4: h_ordering 2, 3, 4, 0, 1; data_index 14; roll_shift  8;

        // Parallel Round 5
            par_round5: h_ordering 1, 2, 3, 4, 0; data_index 12; roll_shift  8
            par_round5: h_ordering 0, 1, 2, 3, 4; data_index 15; roll_shift  5
            par_round5: h_ordering 4, 0, 1, 2, 3; data_index 10; roll_shift 12
            par_round5: h_ordering 3, 4, 0, 1, 2; data_index  4; roll_shift  9
            par_round5: h_ordering 2, 3, 4, 0, 1; data_index  1; roll_shift 12
            par_round5: h_ordering 1, 2, 3, 4, 0; data_index  5; roll_shift  5
            par_round5: h_ordering 0, 1, 2, 3, 4; data_index  8; roll_shift 14
            par_round5: h_ordering 4, 0, 1, 2, 3; data_index  7; roll_shift  6
            par_round5: h_ordering 3, 4, 0, 1, 2; data_index  6; roll_shift  8
            par_round5: h_ordering 2, 3, 4, 0, 1; data_index  2; roll_shift 13
            par_round5: h_ordering 1, 2, 3, 4, 0; data_index 13; roll_shift  6
            par_round5: h_ordering 0, 1, 2, 3, 4; data_index 14; roll_shift  5
            par_round5: h_ordering 4, 0, 1, 2, 3; data_index  0; roll_shift 15
            par_round5: h_ordering 3, 4, 0, 1, 2; data_index  3; roll_shift 13
            par_round5: h_ordering 2, 3, 4, 0, 1; data_index  9; roll_shift 11
            par_round5: h_ordering 1, 2, 3, 4, 0; data_index 11; roll_shift 11;
        );
    }
    #[test]
    fn test_rmd160_compress() {
        let words = [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16];
        let bytes:[u8; 64] = words.into_iter()
            .map(|x:u32| x.to_le_bytes()).flatten()
            .collect::<Vec<u8>>()
            .try_into()
            .unwrap();
        let w = super::H0.to_vec().clone();
        let r = super::compress(&w, words.to_vec());
        let mut r1 = super::H0.clone();
        compress(&mut r1, &bytes);
        assert_eq!(r.to_vec(), r1);
    }
}
