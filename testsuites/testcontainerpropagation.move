module M {
  struct A has drop {
    x: u64,
  }

  struct B has drop {
    x: A,
  }

  struct C has drop {
    x: B
  }

  public fun f() {
    let a = A { x: 1 };
    let b = B { x: a };
    let c = C { x: b };
    let c_ref = &mut c;
    let b_ref = &mut c_ref.x;
    let a_ref = &mut b_ref.x;
    let x_ref = &mut a_ref.x;
    *x_ref = 2;
    assert(c.x.x.x == 2, 1);
  }
}