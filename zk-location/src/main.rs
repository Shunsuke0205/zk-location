use p3_field::Field;
use p3_baby_bear::BabyBear;


fn main() {
    // BabyBearフィールドの要素を生成する正しい方法
    // パラメータ構造体を使い、そこから新しいフィールド要素を作成します。
    // let params = BabyBearParameters; // unused in this demo
    let x = BabyBear::new(100);
    let y = BabyBear::new(101);
    // 足し算
    let sum = x + y;
    
    // 引き算
    let diff = x - y;
    
    // 掛け算
    let prod = x * y;
    
    // 割り算
    let quot = x / y;
    
    println!("x = {:?}", x);
    println!("y = {:?}", y);
    println!("sum (x + y) = {:?}", sum);
    println!("diff (x - y) = {:?}", diff);
    println!("prod (x * y) = {:?}", prod);
    println!("quot (x / y) = {:?}", quot);
}