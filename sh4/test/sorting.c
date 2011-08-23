/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test various sorting algorithms
 * After 2,487,176 instructions executed, r0 should contain 63 = 0x3f */

#include <stdlib.h>

int count = 0;

#define CHECK(OP, TEST)                         \
  if ((TEST)) count+=(OP);


#define ARRAY_SIZE_MAX 4000

int sort_array[ARRAY_SIZE_MAX];
int ARRAY_SIZE;

/*
 * Implement pseudo random function to fill up the tables to sort
 */

#define MT_LEN       624

int mt_index;
unsigned long mt_buffer[MT_LEN]= {
  39634, 62349, 74088, 65564, 16379, 19713, 39153, 69459, 17986, 24537,
  14595, 35050, 40469, 27478, 44526, 67331, 93365, 54526, 22356, 93208,
  30734, 71571, 83722, 79712, 25775, 65178,  7763, 82928, 31131, 30196,
  64628, 89126, 91254, 24090, 25752,  3091, 39411, 73146,  6089, 15630,
  42831, 95113, 43511, 42082, 15140, 34733, 68076, 18292, 69486, 80468,
  80583, 70361, 41047, 26792, 78466,  3395, 17635,  9697, 82447, 31405,
  209, 90404, 99457, 72570, 42194, 49043, 24330, 14939,  9865, 45906,
  5409, 20830,  1911, 60767, 55248, 79253, 12317, 84120, 77772, 50103,
  95836, 22530, 91785, 80210, 34361, 52228, 33869, 94332, 83868, 61672,
  65358, 70469, 87149, 89509, 72176, 18103, 55169, 79954, 72002, 20582,
  72249,  4037, 36192, 40221, 14918, 53437, 60571, 40995, 55006, 10694,
  41692, 40581, 93050, 48734, 34652, 41577,  4631, 49184, 39295, 81776,
  61885, 50796, 96822, 82002,  7973, 52925, 75467, 86013, 98072, 91942,
  48917, 48129, 48624, 48248, 91465, 54898, 61220, 18721, 67387, 66575,
  88378, 84299, 12193,  3785, 49314, 39761, 99132, 28775, 45276, 91816,
  77800, 25734,  9801, 92087,  2955, 12872, 89848, 48579,  6028, 13827,
  24028,  3405,  1178,  6316, 81916, 40170, 53665, 87202, 88638, 47121,
  86558, 84750, 43994,  1760, 96205, 27937, 45416, 71964, 52261, 30781,
  78545, 49201,  5329, 14182, 10971, 90472, 44682, 39304, 19819, 55799,
  14969, 64623, 82780, 35686, 30941, 14622,  4126, 25498, 95452, 63937,
  58697, 31973,  6303, 94202, 62287, 56164, 79157, 98375, 24558, 99241,
  38449, 46438, 91579,  1907, 72146,  5764, 22400, 94490, 49833,  9258,
  62134, 87244, 73348, 80114, 78490, 64735, 31010, 66975, 28652, 36166,
  72749, 13347, 65030, 26128, 49067, 27904, 49953, 74674, 94617, 13317,
  81638, 36566, 42709, 33717, 59943, 12027, 46547, 61303, 46699, 76243,
  46574, 79670, 10342, 89543, 75030, 23428, 29541, 32501, 89422, 87474,
  11873, 57196, 32209, 67663,  7990, 12288, 59245, 83638, 23642, 61715,
  13862, 72778,  9949, 23096,  1791, 19472, 14634, 31690, 36602, 62943,
  8312, 27886, 82321, 28666, 72998, 22514, 51054, 22940, 31842, 54245,
  11071, 44430, 94664, 91294, 35163,  5494, 32882, 23904, 41340, 61185,
  82509, 11842, 86963, 50307,  7510, 32545, 90717, 46856, 86079, 13769,
  7426, 67341, 80314, 58910, 93948, 85738, 69444,  9370, 58194, 28207,
  57696, 25592, 91221, 95386, 15857, 84645, 89659, 80535, 93233, 82798,
  8074, 89810, 48521, 90740,  2687, 83117, 74920, 25954, 99629, 78978,
  20128, 53721,  1518, 40699, 20849,  4710, 38989, 91322, 56057, 58573,
  190, 27157, 83208, 79446, 92987, 61357, 38752, 55424, 94518, 45205,
  23798, 55425, 32454, 34611, 39605, 39981, 74691, 40836, 30812, 38563,
  85306, 57995, 68222, 39055, 43890, 36956, 84861, 63624,  4961, 55439,
  99719, 36036, 74274, 53901, 34643,  6157, 89500, 57514, 93977, 42403,
  95970, 81452, 48873,   784, 58347, 40269, 11880, 43395, 28249, 38743,
  56651, 91460, 92462, 98566, 72062, 18556, 55052, 47614, 80044, 60015,
  71499, 80220, 35750, 67337, 47556, 55272, 55249, 79100, 34014, 17037,
  66660, 78443, 47545, 70736, 65419, 77489, 70831, 73237, 14970, 23129,
  35483, 84563, 79956, 88618, 54619, 24853, 59783, 47537, 88822, 47227,
  9262, 25041, 57862, 19203, 86103,  2800, 23198, 70639, 43757, 52064,
  83760, 31255, 71609, 89887,   940, 54355, 44351, 89781, 58054, 65813,
  66280, 56046, 50526, 33649, 87067,  2697,  6577,  1670, 79636, 84767,
  87021, 82837, 69853, 53419,  9691, 18178, 97312, 20500, 48030, 27256,
  2349, 88955, 52760, 73696, 91510, 38633, 38883, 90419, 26716, 98215,
  93606, 21415, 34843, 12969, 84847,  6280, 95916, 12991,  8262, 58385,
  24274, 87473, 73270, 67800, 80329, 85442, 49028, 16078, 79142, 27216,
  77787,  4965, 75888, 98137, 12118, 38489, 34942, 79467, 97227,  3158,
  91340, 64584,  8977, 30250, 41917, 71444, 93089, 44671, 85280, 85483,
  62500,  9771,  9212,   963, 22337, 99350,  6725, 68898, 17934, 62803,
  32468, 19672, 46055, 61627,   650, 79028, 62988, 72697, 14363, 21884,
  39236, 62399, 64035,  5465, 25404, 90777, 87685, 45027, 95726, 76769,
  26108, 66397, 34505, 12041, 81780, 12787,  5861, 94283, 71545, 35066,
  12602,   490, 85851,  8714, 38100, 99990, 27650, 88249, 27758, 47672,
  10288, 99560,   798, 43192, 55968, 59151,  4003, 94320, 53714, 96459,
  95195, 35561, 28908, 85843, 62150, 18621, 97452, 85980, 56502,  7944,
  9967, 74953,  5591, 34867, 54774, 52449, 23294, 94815, 95124, 35839,
  177, 57742,  9502, 42624, 29017, 94284, 81409, 36904, 54329, 83013,
  94568, 75490, 12138, 24067 };

#define MT_IA           397
#define MT_IB           (MT_LEN - MT_IA)
#define UPPER_MASK      0x80000000
#define LOWER_MASK      0x7FFFFFFF
#define MATRIX_A        0x9908B0DF
#define TWIST(b,i,j)    ((b)[i] & UPPER_MASK) | ((b)[j] & LOWER_MASK)
#define MAGIC(s)        (((s)&1)*MATRIX_A)

unsigned long mt_random() {
  unsigned long * b = mt_buffer;
  int idx = mt_index;
  unsigned long s;
  int i;

  if (idx == MT_LEN*sizeof(unsigned long))
    {
      idx = 0;
      i = 0;
      for (; i < MT_IB; i++) {
        s = TWIST(b, i, i+1);
        b[i] = b[i + MT_IA] ^ (s >> 1) ^ MAGIC(s);
      }
      for (; i < MT_LEN-1; i++) {
        s = TWIST(b, i, i+1);
        b[i] = b[i - MT_IB] ^ (s >> 1) ^ MAGIC(s);
      }

      s = TWIST(b, MT_LEN-1, 0);
      b[MT_LEN-1] = b[MT_IA-1] ^ (s >> 1) ^ MAGIC(s);
    }
  mt_index = idx + sizeof(unsigned long);
  return *(unsigned long *)((unsigned char *)b + idx);
  /* r ^= (r >> 11);
     r ^= (r << 7) & 0x9D2C5680;
     r ^= (r << 15) & 0xEFC60000;
     r ^= (r >> 18);*/
}

unsigned long fill_array()
{
  int indx;
  unsigned long checksum = 0;
  for (indx=0; indx < ARRAY_SIZE; ++indx)
    {
      checksum += sort_array[indx] = mt_random();
    }
  return checksum;
}

typedef int (*CMPFUN)(int, int);

int cmpfun(int a, int b)
{
  if (a > b)
    return 1;
  else if (a < b)
    return -1;
  else
    return 0;
}

/*
 * Qsort() implements quick sort.
 */
#define INSERTION_SORT_BOUND 16 /* boundary point to use insertion sort */

void Qsort(int This[], CMPFUN fun_ptr, unsigned long first, unsigned long last)
{
  unsigned long stack_pointer = 0;
  int first_stack[32];
  int last_stack[32];

  for (;;)
    {
      if (last - first <= INSERTION_SORT_BOUND)
        {
          /* for small sort, use insertion sort */
          unsigned long indx;
          int prev_val = This[first];
          int cur_val;

          for (indx = first + 1; indx <= last; ++indx)
            {
              cur_val = This[indx];
              if ((*fun_ptr)(prev_val, cur_val) > 0)
                {
                  /* out of order: array[indx-1] > array[indx] */
                  unsigned long indx2;
                  This[indx] = prev_val; /* move up the larger item first */

                  /* find the insertion point for the smaller item */
                  for (indx2 = indx - 1; indx2 > first; )
                    {
                      int temp_val = This[indx2 - 1];
                      if ((*fun_ptr)(temp_val, cur_val) > 0)
                        {
                          This[indx2--] = temp_val;
                          /* still out of order, move up 1 slot to make room */
                        }
                      else
                        break;
                    }
                  This[indx2] = cur_val; /* insert the smaller item right here */
                }
              else
                {
                  /* in order, advance to next element */
                  prev_val = cur_val;
                }
            }
        }
      else
        {
          int pivot;

          /* try quick sort */
          {
            int temp;
            unsigned long med = (first + last) >> 1;
            /* Choose pivot from first, last, and median position. */
            /* Sort the three elements. */
            temp = This[first];
            if ((*fun_ptr)(temp, This[last]) > 0)
              {
                This[first] = This[last]; This[last] = temp;
              }
            temp = This[med];
            if ((*fun_ptr)(This[first], temp) > 0)
              {
                This[med] = This[first]; This[first] = temp;
              }
            temp = This[last];
            if ((*fun_ptr)(This[med], temp) > 0)
              {
                This[last] = This[med]; This[med] = temp;
              }
            pivot = This[med];
          }
          {
            unsigned long up;
            {
              unsigned long down;
              /* First and last element will be loop stopper. */
              /* Split array into two partitions. */
              down = first;
              up = last;
              for (;;) {
                do {
                  ++down;
                } while ((*fun_ptr)(pivot, This[down]) > 0);

                do {
                  --up;
                } while ((*fun_ptr)(This[up], pivot) > 0);

                if (up > down) {
                  int temp;
                  /* interchange L[down] and L[up] */
                  temp = This[down]; This[down]= This[up]; This[up] = temp;
                } else
                  break;
              }
            }
            {
              unsigned long len1; /* length of first segment */
              unsigned long len2; /* length of second segment */
              len1 = up - first + 1;
              len2 = last - up;
              /* stack the partition that is larger */
              if (len1 >= len2) {
                first_stack[stack_pointer] = first;
                last_stack[stack_pointer++] = up;

                first = up + 1;
                /*  tail recursion elimination of
                 *  Qsort(This,fun_ptr,up + 1,last)
                 */
              } else {
                first_stack[stack_pointer] = up + 1;
                last_stack[stack_pointer++] = last;

                last = up;
                /* tail recursion elimination of
                 * Qsort(This,fun_ptr,first,up)
                 */
              }
            }
            continue;
          }
          /* end of quick sort */
        }
      if (stack_pointer > 0)
        {
          /* Sort segment from stack. */
          first = first_stack[--stack_pointer];
          last = last_stack[stack_pointer];
        }
      else
        break;
    } /* end for */
}


void HeapSort(int This[], CMPFUN fun_ptr, unsigned long the_len)
{
  /* heap sort */

  unsigned long half;
  unsigned long parent;

  if (the_len <= 1)
    return;

  half = the_len >> 1;
  for (parent = half; parent >= 1; --parent)
    {
      int temp;
      int level = 0;
      unsigned long child;

      child = parent;
      /* bottom-up downheap */

      /* leaf-search for largest child path */
      while (child <= half)
        {
          ++level;
          child += child;
          if ((child < the_len) &&
              ((*fun_ptr)(This[child], This[child - 1]) > 0))
            ++child;
        }
      /* bottom-up-search for rotation point */
      temp = This[parent - 1];
      for (;;)
        {
          if (parent == child)
            break;
          if ((*fun_ptr)(temp, This[child - 1]) <= 0)
            break;
          child >>= 1;
          --level;
        }
      /* rotate nodes from parent to rotation point */
      for (;level > 0; --level)
        {
          This[(child >> level) - 1] =
            This[(child >> (level - 1)) - 1];
        }
      This[child - 1] = temp;
    }

  --the_len;
  do
    {
      int temp;
      int level = 0;
      unsigned long child;

      /* move max element to back of array */
      temp = This[the_len];
      This[the_len] = This[0];
      This[0] = temp;

      child = parent = 1;
      half = the_len >> 1;

      /* bottom-up downheap */

      /* leaf-search for largest child path */
      while (child <= half)
        {
          ++level;
          child += child;
          if ((child < the_len) &&
              ((*fun_ptr)(This[child], This[child - 1]) > 0))
            ++child;
        }
      /* bottom-up-search for rotation point */
      for (;;)
        {
          if (parent == child)
            break;
          if ((*fun_ptr)(temp, This[child - 1]) <= 0)
            break;
          child >>= 1;
          --level;
        }
      /* rotate nodes from parent to rotation point */
      for (;level > 0; --level)
        {
          This[(child >> level) - 1] =
            This[(child >> (level - 1)) - 1];
        }
      This[child - 1] = temp;
    } while (--the_len >= 1);
}


void MergeSort(int This[], CMPFUN fun_ptr, unsigned long the_len)
{
  unsigned long span;
  unsigned long lb;
  unsigned long ub;
  unsigned long indx;
  unsigned long indx2;

  if (the_len <= 1)
    return;

  span = INSERTION_SORT_BOUND;

  /* insertion sort the first pass */
  {
    int prev_val;
    int cur_val;
    int temp_val;

    for (lb = 0; lb < the_len; lb += span)
      {
        if ((ub = lb + span) > the_len) ub = the_len;

        prev_val = This[lb];

        for (indx = lb + 1; indx < ub; ++indx)
          {
            cur_val = This[indx];

            if ((*fun_ptr)(prev_val, cur_val) > 0)
              {
                /* out of order: array[indx-1] > array[indx] */
                This[indx] = prev_val; /* move up the larger item first */

                /* find the insertion point for the smaller item */
                for (indx2 = indx - 1; indx2 > lb;)
                  {
                    temp_val = This[indx2 - 1];
                    if ((*fun_ptr)(temp_val, cur_val) > 0)
                      {
                        This[indx2--] = temp_val;
                        /* still out of order, move up 1 slot to make room */
                      }
                    else
                      break;
                  }
                This[indx2] = cur_val; /* insert the smaller item right here */
              }
            else
              {
                /* in order, advance to next element */
                prev_val = cur_val;
              }
          }
      }
  }

  /* second pass merge sort */
  {
    unsigned long median;
    int* aux;

    aux = (int*) malloc(sizeof(int) * the_len / 2);

    while (span < the_len)
      {
        /* median is the start of second file */
        for (median = span; median < the_len;)
          {
            indx2 = median - 1;
            if ((*fun_ptr)(This[indx2], This[median]) > 0)
              {
                /* the two files are not yet sorted */
                if ((ub = median + span) > the_len)
                  {
                    ub = the_len;
                  }

                /* skip over the already sorted largest elements */
                while ((*fun_ptr)(This[--ub], This[indx2]) >= 0)
                  {
                  }

                /* copy second file into buffer */
                for (indx = 0; indx2 < ub; ++indx)
                  {
                    *(aux + indx) = This[++indx2];
                  }
                --indx;
                indx2 = median - 1;
                lb = median - span;
                /* merge two files into one */
                for (;;)
                  {
                    if ((*fun_ptr)(*(aux + indx), This[indx2]) >= 0)
                      {
                        This[ub--] = *(aux + indx);
                        if (indx > 0) --indx;
                        else
                          {
                            /* second file exhausted */
                            for (;;)
                              {
                                This[ub--] = This[indx2];
                                if (indx2 > lb) --indx2;
                                else goto mydone; /* done */
                              }
                          }
                      }
                    else
                      {
                        This[ub--] = This[indx2];
                        if (indx2 > lb) --indx2;
                        else
                          {
                            /* first file exhausted */
                            for (;;)
                              {
                                This[ub--] = *(aux + indx);
                                if (indx > 0) --indx;
                                else goto mydone; /* done */
                              }
                          }
                      }
                  }
              }
          mydone:
            median += span + span;
          }
        span += span;
      }

    free(aux);
  }
}

/* Calculated from the combinations of  9 * (4^n - 2^n) + 1,
 * and  4^n - 3 * 2^n + 1
 */
unsigned long hop_array[] =
  {
    1,
    5,
    19,
    41,
    109,
    209,
    505,
    929,
    2161,
    3905,
    8929,
    16001,
    36289,
    64769,
    146305,
    260609,
    587521,
    1045505,
    2354689,
    4188161,
    9427969,
    16764929,
    37730305,
    67084289,
    150958081,
    268386305,
    603906049,
    1073643521,
    0x8FFDC001,
    0xffffffff };


void ShellSort(int This[], CMPFUN fun_ptr, unsigned long the_len)
{
  /* shell sort */

  int level;

  for (level = 0; the_len > hop_array[level]; ++level);

  do
    {
      unsigned long dist;
      unsigned long indx;

      dist = hop_array[--level];
      for (indx = dist; indx < the_len; ++indx)
        {
          int cur_val;
          unsigned long indx2;

          cur_val = This[indx];
          indx2 = indx;
          do
            {
              int early_val;
              early_val = This[indx2 - dist];
              if ((*fun_ptr)(early_val, cur_val) <= 0)
                break;
              This[indx2] = early_val;
              indx2 -= dist;
            } while (indx2 >= dist);
          This[indx2] = cur_val;
        }
    } while (level >= 1);
}


void InsertionSort(int This[], CMPFUN fun_ptr, unsigned long the_len)
{
  /* insertion sort */

  unsigned long indx;
  int cur_val;
  int prev_val;

  if (the_len <= 1)
    return;

  prev_val = This[0];

  for (indx = 1; indx < the_len; ++indx)
    {
      cur_val = This[indx];
      if ((*fun_ptr)(prev_val, cur_val) > 0)
        {
          /* out of order: array[indx-1] > array[indx] */
          unsigned long indx2;
          This[indx] = prev_val; /* move up the larger item first */

          /* find the insertion point for the smaller item */
          for (indx2 = indx - 1; indx2 > 0;)
            {
              int temp_val = This[indx2 - 1];
              if ((*fun_ptr)(temp_val, cur_val) > 0)
                {
                  This[indx2--] = temp_val;
                  /* still out of order, move up 1 slot to make room */
                }
              else
                break;
            }
          This[indx2] = cur_val; /* insert the smaller item right here */
        }
      else
        {
          /* in order, advance to next element */
          prev_val = cur_val;
        }
    }
}

void BubbleSort(int This[], CMPFUN fun_ptr, unsigned long ub)
{
  /* bubble sort */

  unsigned long indx;
  unsigned long indx2;
  int temp;
  int temp2;
  int flipped;

  if (ub <= 1)
    return;

  indx = 1;
  do
    {
      flipped = 0;
      for (indx2 = ub - 1; indx2 >= indx; --indx2)
        {
          temp = This[indx2];
          temp2 = This[indx2 - 1];
          if ((*fun_ptr)(temp2, temp) > 0)
            {
              This[indx2 - 1] = temp;
              This[indx2] = temp2;
              flipped = 1;
            }
        }
    } while ((++indx < ub) && flipped);
}

int ValidSort(int array[], unsigned long cs)
{
  int indx;
  unsigned long checksum2 = 0;

  for (indx=1; indx < ARRAY_SIZE; ++indx)
    {
      if (sort_array[indx - 1] > sort_array[indx])
        {
          return 0;
        }
    }
  for (indx=0; indx < ARRAY_SIZE; ++indx)
    checksum2 += sort_array[indx];

  return (checksum2 == cs) ? 1: 0;
}

int main()
{
  ARRAY_SIZE = 400;

  unsigned long checksum1;

  /* quick sort */
  checksum1 = fill_array();
  Qsort(sort_array, cmpfun, 0,  ARRAY_SIZE - 1);
  CHECK(1,!(ValidSort(sort_array, checksum1) == 0));

  /* heap sort */
  checksum1 = fill_array();
  HeapSort(sort_array, cmpfun, ARRAY_SIZE);
  CHECK(2,!(ValidSort(sort_array, checksum1) == 0));

  /* merge sort */
  checksum1 = fill_array();
  MergeSort(sort_array, cmpfun, ARRAY_SIZE);
  CHECK(4,!(ValidSort(sort_array, checksum1) == 0));

  /* shell sort */
  checksum1 = fill_array();
  ShellSort(sort_array, cmpfun, ARRAY_SIZE);
  CHECK(8,!(ValidSort(sort_array, checksum1) == 0));

  ARRAY_SIZE = 200; /* following algorithms are slower */

  /* insertion sort */
  checksum1 = fill_array();
  InsertionSort(sort_array, cmpfun, ARRAY_SIZE);
  CHECK(16,!(ValidSort(sort_array, checksum1) == 0));

  /* bubble sort */
  checksum1 = fill_array();
  BubbleSort(sort_array, cmpfun, ARRAY_SIZE);
  CHECK(32,!(ValidSort(sort_array, checksum1) == 0));

  return count;
}
