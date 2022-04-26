module quant_basic();


   wire zero;

   assign zero = 0;   
   
   //-----------------------------------------------------------------------------
   // Ignore non-index
   //-----------------------------------------------------------------------------
   wire [1:0] {L} a;

   wire [1:0] {|i| LH zero} b;


   //should pass
   assign a[0] = b[0];

   //should pass
   assign a[1] = b[1];


   //-----------------------------------------------------------------------------
   // Use index
   //-----------------------------------------------------------------------------
   wire [1:0] {L} c;

   wire [1:0] {|i| LH i} d;


   //should pass
   assign c[0] = d[0];

   //should fail
   assign c[1] = d[1];


   //-----------------------------------------------------------------------------
   // Quantifying over indexing expression (1)
   //-----------------------------------------------------------------------------
   wire [1:0] {L} e;

   wire [1:0] {|i| LH i} f;

   wire       g;

   wire       g2;

   wire       {H} g3;
   
   assign g2 = 1;
   assign g3 = 0;
   
   //should fail
   assign e[0] = f[g];
   //should fail
   assign e[0] = f[g2];
   //should fail b/c L(g3) = H
   assign e[0] = f[g3];
   

   //-----------------------------------------------------------------------------
   // Quantifying over indexing expression (2)
   //-----------------------------------------------------------------------------
   wire [1:0] {L} h;

   wire [1:0] {|i| LH zero} i;

   wire       j;


   //should pass
   assign h[0] = i[j];


   //-----------------------------------------------------------------------------
   // Quantifying over indexing expression (3)
   //-----------------------------------------------------------------------------
   wire [1:0] {|i| LH i} k;

   wire [1:0] {|i| LH i} l;


   //should pass
   assign k[0] = l[0];

   //should pass
   assign k[1] = l[1];

   //should pass
   assign k[g2] = l[g2];
   

   //-----------------------------------------------------------------------------
   // Quantified Join Types (1)
   //-----------------------------------------------------------------------------
   wire [1:0] {|i| LH i} m;

   wire [1:0] {|i| LH i} n;

   wire [1:0] {H} o;


   //should fail
   assign m[0] = n[0] + o[0];

   //should pass
   assign m[1] = n[1] + o[1];


   //-----------------------------------------------------------------------------
   // Quantified Join Types (1)
   //-----------------------------------------------------------------------------
   wire [1:0] {|i| LH i} p;

   wire [1:0] {|i| LH i} q;

   wire [1:0] {|i| LH i} r;


   //should pass
   assign p[0] = q[0] + r[0];

   //should pass
   assign p[1] = q[1] + r[1];



endmodule
