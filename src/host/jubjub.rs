use lazy_static::lazy_static;
use crate::utils::bn_to_field;
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::pairing::bn256::Bn256;
use std::ops::{SubAssign, MulAssign, AddAssign};
use ff::Field;
use num_bigint::BigUint;

use ff_ce::BitIterator;
use franklin_crypto::alt_babyjubjub::fs;

lazy_static! {
    static ref D_BIG: BigUint = BigUint::parse_bytes(b"12181644023421730124874158521699555681764249180949974110617291017600649128846", 10).unwrap();
    static ref D: Fr = bn_to_field(&(D_BIG));
    static ref A_BIG: BigUint = BigUint::parse_bytes(b"21888242871839275222246405745257275088548364400416034343698204186575808495616", 10).unwrap();
    static ref A: Fr = bn_to_field(&(A_BIG));
    pub static ref Q: BigUint = BigUint::parse_bytes(
        b"21888242871839275222246405745257275088548364400416034343698204186575808495617",10
    ).unwrap();
}

#[derive(Clone, Debug)]
pub struct PointProjective {
    pub x: Fr,
    pub y: Fr,
    pub z: Fr,
}

impl PointProjective {
    pub fn affine(&self) -> Point {
        if self.z.is_zero_vartime() {
            return Point {
                x: Fr::zero(),
                y: Fr::zero(),
            };
        }

        let zinv = self.z.invert().unwrap();
        let mut x = self.x;
        x.mul_assign(&zinv);
        let mut y = self.y;
        y.mul_assign(&zinv);

        Point { x, y }
    }

    #[allow(clippy::many_single_char_names)]
    pub fn add(&self, q: &PointProjective) -> PointProjective {
        // add-2008-bbjlp https://hyperelliptic.org/EFD/g1p/auto-twisted-projective.html#addition-add-2008-bbjlp
        let mut a = self.z;
        a.mul_assign(&q.z);
        let mut b = a;
        b.square();
        let mut c = self.x;
        c.mul_assign(&q.x);
        let mut d = self.y;
        d.mul_assign(&q.y);
        let mut e = *D;
        e.mul_assign(&c);
        e.mul_assign(&d);
        let mut f = b;
        f.sub_assign(&e);
        let mut g = b;
        g.add_assign(&e);
        let mut x1y1 = self.x;
        x1y1.add_assign(&self.y);
        let mut x2y2 = q.x;
        x2y2.add_assign(&q.y);
        let mut aux = x1y1;
        aux.mul_assign(&x2y2);
        aux.sub_assign(&c);
        aux.sub_assign(&d);
        let mut x3 = a;
        x3.mul_assign(&f);
        x3.mul_assign(&aux);
        let mut ac = *A;
        ac.mul_assign(&c);
        let mut dac = d;
        dac.sub_assign(&ac);
        let mut y3 = a;
        y3.mul_assign(&g);
        y3.mul_assign(&dac);
        let mut z3 = f;
        z3.mul_assign(&g);

        PointProjective {
            x: x3,
            y: y3,
            z: z3,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Point {
    pub x: Fr,
    pub y: Fr,
}

impl Point {
    pub fn identity() -> Self {
        Point {
            x: Fr::zero(),
            y: Fr::one(),
        }
    }
    pub fn zero() -> Self {
        Point {
            x: Fr::zero(),
            y: Fr::one(),
        }
    }
    pub fn projective(&self) -> PointProjective {
        PointProjective {
            x: self.x,
            y: self.y,
            z: Fr::one(),
        }
    }

    pub fn add(&self, other: &Point) -> Point{
        self.projective().add(&other.projective()).affine()
    }

    pub fn mul_scalar(&self, n: &BigUint) -> Point {
        let mut r = Point::zero();
        let mut exp = self.clone();
        let b = n.to_bytes_le();
        //little-end wise, like 6, it is 0,1,1 sequence
        for i in 0..n.bits() {
            if test_bit(&b, i.try_into().unwrap()) {
                r = r.add(&exp);
            }
            exp = exp.add(&exp);
        }
        r
    }


    pub fn mul_scalar_fs(&self, scalar: fs::Fs) -> Point {
        let mut r = Point::zero();
        //big-end wise, like 6, it is 1,1,0 sequence
        for b in BitIterator::<fs::FsRepr>::new(scalar.into()) {
            r = r.add(&r);
            if b {
                r = r.add(self);
            }
        }
        r
    }
}

pub fn test_bit(b: &[u8], i: usize) -> bool {
    b[i / 8] & (1 << (i % 8)) != 0
}

#[cfg(test)]

mod tests {
    use super::{Point, PointProjective};
    use crate::adaptor::fr_to_args;
    use crate::host::{ExternalHostCallEntry, ExternalHostCallEntryTable, ForeignInst};
    use crate::utils::field_to_bn;
    use halo2_proofs::arithmetic::FieldExt;
    use halo2_proofs::pairing::bn256::pairing;
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::pairing::group::Group;
    use num_bigint::BigUint;

    use std::fs::File;
    use std::ops::Add;

    fn babyarg_to_args(v: &Fr, op: ForeignInst) -> Vec<ExternalHostCallEntry> {
        fr_to_args(*v, 4, 64, op)
    }

    fn babysum_to_args(x: Point, y: Point, z: Point) -> Vec<ExternalHostCallEntry> {
        let mut ret = vec![
            babyarg_to_args(&x.x, ForeignInst::JubjubSumPush),
            babyarg_to_args(&x.y, ForeignInst::JubjubSumPush),
            babyarg_to_args(&y.x, ForeignInst::JubjubSumPush),
            babyarg_to_args(&y.y, ForeignInst::JubjubSumPush),
            babyarg_to_args(&z.x, ForeignInst::JubjubSumResult),
            babyarg_to_args(&z.y, ForeignInst::JubjubSumResult),
        ]
            .into_iter()
            .flatten()
            .collect();
        ret
    }

    struct JubjubSumContext {
        acc: Point,
        operand: Point,
        coeff: [u64; 4],
    }

    fn generate_entries_single_round(context: &mut JubjubSumContext) -> Vec<ExternalHostCallEntry> {
        todo!()
    }

    #[test]
    fn generate_jubjub_sum_input() {
        let identity = Point::identity();
        let identity_proj = identity.projective();
        let entries = babysum_to_args(
            Point::identity(),
            Point::identity(),
            identity_proj.add(&identity_proj).affine(),
        );
        let table = ExternalHostCallEntryTable(entries);
        let file = File::create("jubjubsumtest.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
        assert_eq!(identity, identity_proj.add(&identity_proj).affine());
    }
    use ff_ce::PrimeField;
    use franklin_crypto::alt_babyjubjub::fs;
    use franklin_crypto::eddsa::{PublicKey,PrivateKey};
    use franklin_crypto::jubjub::ToUniform;
    use crate::utils::bn_to_field;
    use std::str::FromStr;
    #[test]
    pub fn verify_alt_jubjub_signature() {
        let msg = b"Foo bar";

        // pad with zeroes to match representation length
        let mut msg_padded: Vec<u8> = msg.iter().cloned().collect();
        msg_padded.resize(32, 0u8);

        let c = fs::Fs::to_uniform_32(msg_padded.as_ref());
        // let mut c_bytes = [0u8; 32];
        // c.into_repr().write_le(& mut c_bytes[..]).expect("get LE bytes of signature S");
        // let c_repr_bigint = BigInt::from_signed_bytes_le(&c_bytes);
        // println!("c {}",c_repr_bigint.to_str_radix(10));

        let vk = Point {
            x: bn_to_field(&(BigUint::parse_bytes(b"139f1d319d2a51a1938aef20ae4aa05b4bacef0c95ec2acf6d70b0430bed7808", 16).unwrap())),
            y: bn_to_field(&(BigUint::parse_bytes(b"023abdc9dac65b2e858cf258c0a9b0c2c8a83a86ec2ebbaab8fdb5169b262597", 16).unwrap())),
        };

        let sig_r = Point {
            x: bn_to_field(&(BigUint::parse_bytes(b"00d711880dcccc0767dad1aa321fa2f54462c0d91e7c708836b5ac274215e4ca", 16).unwrap())),
            y: bn_to_field(&(BigUint::parse_bytes(b"303438ab520086fb5e723bdc3c5e0f6a99b7d1caca0b8871ce16ab467d4baf5c", 16).unwrap())),
        };
        let p_g = Point {
            x: bn_to_field(&(BigUint::parse_bytes(b"2ef3f9b423a2c8c74e9803958f6c320e854a1c1c06cd5cc8fd221dc052d76df7", 16).unwrap())),
            y: bn_to_field(&(BigUint::parse_bytes(b"05a01167ea785d3f784224644a68e4067532c815f5f6d57d984b5c0e9c6c94b7", 16).unwrap())),
        };
        let sig_s_str = "1902101563350775171813864964289368622061698554691074493911860015574812994359";
        let sig_s = fs::Fs::from_str(sig_s_str).unwrap();

        // 0 = c . vk + R -S . P_G that requires all points to be in the same group
        // self.0
        //     .mul(c, params)
        //     .add(&sig.r, params)
        //     .add(
        //         &params.generator(p_g).mul(sig.s, params).negate().into(),
        //         params,
        //     )
        //     .eq(&Point::zero())
        let lhs = vk.mul_scalar_fs(c).add(&sig_r);
        let rhs = p_g.mul_scalar_fs(sig_s);
        // println!("lhs x={},y={}",lhs.x,lhs.y);
        // println!("rhs x={},y={}",rhs.x,rhs.y);
        assert_eq!(lhs,rhs);

        let c = BigUint::from_bytes_le(&msg_padded);
        let sig_s = BigUint::from_str(sig_s_str).unwrap();
        let lhs = vk.mul_scalar(&c).add(&sig_r);
        let rhs = p_g.mul_scalar(&sig_s);
        // println!("lhs x={},y={}",lhs.x,lhs.y);
        // println!("rhs x={},y={}",rhs.x,rhs.y);
        assert_eq!(lhs,rhs)

    }
    use rand::{ SeedableRng, thread_rng};
    use rand::{Rng};
    use franklin_crypto::bellman::pairing::bn256::Bn256;
    use franklin_crypto::jubjub::FixedGenerators;
    use franklin_crypto::alt_babyjubjub::AltJubjubBn256;


    #[test]
    pub fn verify_alt_jubjub() {
        let rng = &mut thread_rng();
        let sk = PrivateKey::<Bn256>(rng.gen());
        let params = AltJubjubBn256::new();
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let pk = PublicKey::from_private(&sk, p_g, &params);

       // println!("vk={:?}",pk.0.into_xy().0);

        let vk = Point {
            x: bn_to_field(&(BigUint::parse_bytes(b"139f1d319d2a51a1938aef20ae4aa05b4bacef0c95ec2acf6d70b0430bed7808", 16).unwrap())),
            y: bn_to_field(&(BigUint::parse_bytes(b"023abdc9dac65b2e858cf258c0a9b0c2c8a83a86ec2ebbaab8fdb5169b262597", 16).unwrap())),
        };


        // let fr_str = "1902101563350775171813864964289368622061698554691074493911860015574812994359";
        // let fs_str = "1902101563350775171813864964289368622061698554691074493911860015574812994359";

        // ;
        let mut result = [0u8; 32];
        let repr = pk.0.into_xy().0.into_repr();
        repr.write_le(result.as_mut_slice()).unwrap();
        let fr_s = BigUint::from_bytes_le(&result);
        let fs_s = fs::Fs::to_uniform_32(&result);
        // let fs_s = BigUint::from_str(fs_str).unwrap();
        // println!("fr_s={},fs={:?}",fr_s.to_str_radix(16),fs_s.to_string());
        let lhs = vk.mul_scalar(&fr_s);
        let rhs = vk.mul_scalar_fs(fs_s);
        // println!("lhs x={},y={}",lhs.x,lhs.y);
        // println!("rhs x={},y={}",rhs.x,rhs.y);
        assert_eq!(lhs,rhs)

    }

    #[test]
    fn test_mul(){
        for i in 0..50000{
            verify_alt_jubjub()
        }
    }

    #[test]
    pub fn verify_alt_jubjub_mul() {
        let vk = Point {
            x: bn_to_field(&(BigUint::parse_bytes(b"139f1d319d2a51a1938aef20ae4aa05b4bacef0c95ec2acf6d70b0430bed7808", 16).unwrap())),
            y: bn_to_field(&(BigUint::parse_bytes(b"023abdc9dac65b2e858cf258c0a9b0c2c8a83a86ec2ebbaab8fdb5169b262597", 16).unwrap())),
        };

        let fr_str = "2736030358979909402780800718157159386076813972158567259200215660948447373041";
        let fs_str = "0";

        let fr_s = BigUint::from_str(&fr_str).unwrap();
        let fs_s = BigUint::from_str(&fs_str).unwrap();
        // println!("fr_s={},fs={:?}",fr_s.to_str_radix(16),fs_s.to_string());
        let lhs = vk.mul_scalar(&fr_s);
        let rhs = vk.mul_scalar(&fs_s);
        // println!("lhs x={},y={}",lhs.x,lhs.y);
        // println!("rhs x={},y={}",rhs.x,rhs.y);
        assert_eq!(lhs,rhs)

    }

    use ff_ce::PrimeFieldRepr;
    #[test]
    fn generate_test_mul() {
        use num_bigint::BigInt;
        let msg = b"Foo bar";

        // pad with zeroes to match representation length
        let mut msg_padded: Vec<u8> = msg.iter().cloned().collect();
        msg_padded.resize(32, 0u8);
        //
        let c = fs::Fs::to_uniform_32(msg_padded.as_ref());
        // let c = fs::Fs::from_str("2").unwrap();
        let mut c_bytes = [0u8; 32];
        c.into_repr().write_le(& mut c_bytes[..]).expect("get LE bytes of signature S");
        let c_repr_bigint = BigInt::from_signed_bytes_le(&c_bytes);
        println!("c {}",c_repr_bigint.to_str_radix(10));


        let p_g = Point {
            x: bn_to_field(&(BigUint::parse_bytes(b"2ef3f9b423a2c8c74e9803958f6c320e854a1c1c06cd5cc8fd221dc052d76df7", 16).unwrap())),
            y: bn_to_field(&(BigUint::parse_bytes(b"05a01167ea785d3f784224644a68e4067532c815f5f6d57d984b5c0e9c6c94b7", 16).unwrap())),
        };

        let rhs = p_g.mul_scalar_fs(c);

        //c=32195221423877958
        //x=2b7caecadf67c405983ab5ba77e8e2f921158850fee4d0962751642010fdace4,y=15d6b5dca01dfbe7e549389628242504c60a0be8ae36dd4de1fbb5c461bc067e
        //dec:x=19669747898413870458863629521161089277913689400039595142733762095585723002084,y=9877930256250505639648328887241932676754586687658209502285904431386979993214
        println!("rhs x={},y={}",rhs.x,rhs.y);

    }

    #[test]
    fn generate_test_add() {

        let vk = Point {
            x: bn_to_field(&(BigUint::parse_bytes(b"01fc44267c07b1ebf40c09633c0e7cd3eb21749b315d960f1ff88cca4a95b90c", 16).unwrap())),
            y: bn_to_field(&(BigUint::parse_bytes(b"0f5e2196329baa2d5bbeaf2e644b8eabef581ab5b34711ee381a2a50b0259c1c", 16).unwrap())),
        };
        // let sig_r = Point {
        //     x: bn_to_field(&(BigUint::parse_bytes(b"2ef3f9b423a2c8c74e9803958f6c320e854a1c1c06cd5cc8fd221dc052d76df7", 16).unwrap())),
        //     y: bn_to_field(&(BigUint::parse_bytes(b"05a01167ea785d3f784224644a68e4067532c815f5f6d57d984b5c0e9c6c94b7", 16).unwrap())),
        // };
        let sig_r = Point {
            x: bn_to_field(&(BigUint::parse_bytes(b"2ef3f9b423a2c8c74e9803958f6c320e854a1c1c06cd5cc8fd221dc052d76df7", 16).unwrap())),
            y: bn_to_field(&(BigUint::parse_bytes(b"05a01167ea785d3f784224644a68e4067532c815f5f6d57d984b5c0e9c6c94b7", 16).unwrap())),
        };
        //rhs x=24a751121f7d0d785935d55306ebfe453ad55fe3435201ab95615bdb829f0316,y=08ee66c2e788d6f56d9457aff9101426b9ad86bb39e8353d719cc02fe7fc9a53
        //dec:x=16578885538864834913634152914207572829284688953553409301338692898630452314902,y=4039721622823844597861764938277547409353264496911078152703637653498156063315
        let rhs = vk.add(&sig_r);

        println!("rhs x={},y={}",rhs.x,rhs.y);

    }


}
