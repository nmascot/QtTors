typedef ulong bit_array __attribute__ ((vector_size (16)));
#define EXT0(a) ((ulong)a[0])
#define EXT(a,i) ((ulong)a[i])
#define AND(a,b) ((a)&(b))
#define TEST(a) (EXT0(a) || EXT1(a))
#define RBA(a) ((bit_array){((long) a), ((long) a)})

int main(void)
{
  bit_array x = RBA(1L), y = RBA(3L);
  ulong t = TEST(AND(x,y));
  (void) t;
  return 0;
}
