/*
         This OS/2 1.3 program will generate a three dimensional maze on a VGA
    display.  A different random number seed will produce a different maze.

         Written on March 7, 1992 by James L. Dean
                                     406 40th Street
                                     New Orleans, LA 70124
*/
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <malloc.h>
#include <memory.h>
#include <stdlib.h>
#include <conio.h>
#include <dos.h>
#define INCL_BASE
#include <os2.h>

#define TRUE 1
#define FALSE 0

/* screen constants */
#define WIDTH_OF_SCREEN           8.0
#define HEIGHT_OF_SCREEN          6.0 /* same units as WIDTH_OF_SCREEN */

/* graphics constants */
#define NUM_X_PIXELS            640
#define NUM_Y_PIXELS            480
#define NUM_COLORS               16
#define RGB_INCREMENT             4     /* 64/NUM_COLORS */
#define stack_size            32767
#define NUM_CELLS             38400     /* NUM_X_PIXELS*NUM_Y_PIXELS/8 */
#define VGA_control           0x3ce     /* graphics controller control port */
#define VGA_control_data      0x3cf     /* graphics controller data port */
#define VGA_read_map           0x04     /* read map register in graphics port */
#define VGA_mode               0x05     /* mode register in graphics port */
#define VGA_bit_mask           0x08     /* bitmask register in graphics port */     
#define VGA_sequence          0x3c4     /* sequencer control port */
#define VGA_sequence_data     0x3c5     /* sequencer data port   */
#define VGA_map_mask           0x02     /* map mask register in sequencer */

/* maze constants */
#define NUM_COLUMNS             24
#define MAX_X                   48      /* 2*NUM_COLUMNS */
#define MAX_X_PLUS_1            49      /* MAX_X+1 */
#define MAX_X_LESS_1            47      /* MAX_X-1 */
#define NUM_ROWS                18
#define MAX_Y                   36      /* 2*NUM_ROWS */
#define MAX_Y_PLUS_1            37      /* MAX_Y+1 */
#define MAX_Y_LESS_1            35      /* MAX_Y-1 */
#define NUM_ROOMS_IN_MAZE      432      /* NUM_ROWS*NUM_COLUMNS */
#define RESOLUTION               4      /* larger numbers give more detail
                                           but take more time and memory */

typedef struct
          {
            int   x;
            int   y;
          } box_rec;

typedef struct
          {
            unsigned char red;
            unsigned char green;
            unsigned char blue;
          } rgb_rec;

typedef struct
          {
            double x;
            double y;
            double z;
          } vertex_rec;

static void   add_room(void);
static void   adjust_perspective(int,int,float huge *,float huge *,float huge *,
               double,double,double,double,double);
static void   clear_screen(void);
static void   evaluate_and_transform(double,double,double,double,int,int,
               double,double,float huge *,float huge *,float huge *,double *,
               double *,double *,double *,double *,vertex_rec *,vertex_rec *,
               int huge *,int huge *,unsigned char huge *);
static double f(double,double);
static void   free_memory(float huge **,float huge **,float huge **,int huge **,
               int huge **,unsigned char huge **,unsigned char huge **);
static void   generate_maze(void);
static void   get_cursor(USHORT *,USHORT *,VIOCURSORINFO *);
static void   hash(int *,int *,int *,int *,int *,int *,int *,int *);
static void   increment(int *,int *,int *,int *,int *,int *,int *,int *);
       void   main(void);
static int    memory_allocated(long,float huge **,float huge **,float huge **,
               int huge **,int huge **,unsigned char huge **,
               unsigned char huge **);
static void   mode_thread(void);
static int    num_rooms_in_solution(void);
static void   plot(int,int huge *,int,int huge *,long,float huge *,float huge *,
               double,double,double,double,unsigned char huge *,
               unsigned char huge *,int);
static void   save_redraw_thread(void);
static void   set_cursor_position(USHORT,USHORT);
static void   set_cursor_type(VIOCURSORINFO *);
static void   set_initial_video_mode(void);
static void   set_pixel(int,int,short);
static void   shade(int,int,float huge *,float huge *,float huge *,
               unsigned char huge *,vertex_rec *);
static void   sort_back_to_front(long,float huge *,int huge *,int huge *);
static void   titillate(void);
static int    VGA_640_480_16(void);

static USHORT        cursor_column;
static USHORT        cursor_row;
static int           delta_x [4] [24];
static int           delta_y [4] [24];
       VIOCURSORINFO initial_cursor_type;
static char          page [MAX_Y_PLUS_1] [MAX_X_PLUS_1];
static int           r_n [8];
static int           r_n_index_1;
static int           r_n_index_2;
static int           tem_int;
static char          titillator [4] = { '|', '/', '-', '\\' };
       VIOCURSORINFO titillator_cursor_type;
static int           titillator_index;
static int           x_maze;
static int           x_next;
static int           x_wall;
static int           y_maze;
static int           y_next;
static int           y_wall;

/* video globals */

       VIOMODEINFO   default_video_mode;
       PVIOPALSTATE  invisible_palette;
       BYTE          invisible_palette_byte [38];
       VIOCOLORREG   maze_color;
       PVIOPALSTATE  maze_palette;
       BYTE          maze_palette_byte [38];
static rgb_rec       maze_rgb [16];
       VIOMODEINFO   maze_video_mode;
static int           mode_id;
static char          mode_thread_stack [stack_size];
       VIOPHYSBUF    phys_buf;
static char          save_redraw_thread_stack [stack_size];
static int           save_redraw_id;
static unsigned char scr_lock;    
static int           VGA_base_adr;
static long huge     *video_plane [4];  /* save area for video planes */

void main()
  {
    static unsigned char huge *color;
    static vertex_rec         light;
    static vertex_rec         light_prime;
    static int                num_x_divisions;
    static long               num_primes;
    static int                num_y_divisions;
    static int                response;
    static double             rotation;
    static unsigned char huge *base_z;
    static double             tilt;
    static int huge           *x_division_index;
    static double             x_max;
    static double             x_min;
    static float huge         *x_prime;
    static double             x_prime_max;
    static int huge           *y_division_index;
    static double             y_max;
    static double             y_min;
    static float huge         *y_prime;
    static double             y_prime_max;
    static double             y_prime_min;
    static float huge         *z_prime;
    static double             z_prime_max;
    static double             z_prime_min;

    num_x_divisions=RESOLUTION*(MAX_Y+2)+1;
    num_y_divisions=RESOLUTION*(MAX_X+2)+1;
    num_primes=(long) num_x_divisions;
    num_primes*=((long) num_y_divisions);
    if (memory_allocated(num_primes,&x_prime,&y_prime,
     &z_prime,&x_division_index,&y_division_index,&color,&base_z))
      {
        clear_screen();
        printf("                                 Maze Generator\n\n\n\n");
        printf(
        "     After the maze is displayed, press \"S\" to see the solution.\n");
        generate_maze();
        x_min=1.0;
        x_max=(double) num_x_divisions;
        y_min=1.0;
        y_max=(double) num_y_divisions;
        rotation=0.0;
        tilt=30.0; /* must be < 90.0 if solution is to be displayed correctly */
        light.x=0.0;
        light.y=-1.0;
        light.z=3.0;
        evaluate_and_transform(x_min,x_max,y_min,y_max,num_x_divisions,
         num_y_divisions,rotation,tilt,x_prime,y_prime,z_prime,&x_prime_max,
         &y_prime_min,&y_prime_max,&z_prime_min,&z_prime_max,&light,
         &light_prime,x_division_index,y_division_index,base_z);
        shade(num_x_divisions,num_y_divisions,x_prime,y_prime,z_prime,color,
         &light_prime);
        adjust_perspective(num_x_divisions,num_y_divisions,x_prime,y_prime,
         z_prime,x_prime_max,y_prime_min,y_prime_max,z_prime_min,z_prime_max);
        sort_back_to_front(num_primes,x_prime,x_division_index,
         y_division_index);
        if (VGA_640_480_16())
          {
            plot(num_x_divisions,x_division_index,num_y_divisions,
             y_division_index,num_primes,y_prime,z_prime,y_prime_min,
             y_prime_max,z_prime_min,z_prime_max,color,base_z,FALSE);
            fflush(stdin);
            response=getch();
            fflush(stdin);
            if ((response == (int) 's') || (response == (int) 'S'))
              {
                plot(num_x_divisions,x_division_index,num_y_divisions,
                 y_division_index,num_primes,y_prime,z_prime,y_prime_min,
                 y_prime_max,z_prime_min,z_prime_max,color,base_z,TRUE);
                fflush(stdin);
                response=getch();
                fflush(stdin);
              }
            set_initial_video_mode();
          }
        else
          printf("? 640 x 480 x 16 VGA mode is not available\n");
        set_cursor_type(&initial_cursor_type);
        free_memory(&x_prime,&y_prime,&z_prime,&x_division_index,
         &y_division_index,&color,&base_z);
      }
    else
      printf("? not enough memory\n");
    return;
  }

static void clear_screen()
  {
    unsigned char fill [2];
    VIOMODEINFO   video_mode_info;

    video_mode_info.cb=(unsigned int) 12;
    VioGetMode(&video_mode_info,(HVIO) 0);
    fill[0]=(unsigned char) ' ';
    fill[1]=(unsigned char) 7;
    VioScrollUp((USHORT) 0,(USHORT) 0,
     (USHORT) (video_mode_info.row-1),
     (USHORT) (video_mode_info.col-1),
     (USHORT) 0xffff,(PBYTE) &fill[0],(HVIO) 0);
    VioSetCurPos((USHORT) 0,(USHORT) 0,(HVIO) 0);
    return;
  }

static void get_cursor(cursor_row,cursor_column,cursor_type)
  USHORT        *cursor_row;
  USHORT        *cursor_column;
  VIOCURSORINFO *cursor_type;
    {
      VioGetCurPos((PUSHORT) cursor_row,(PUSHORT) cursor_column,(HVIO) 0);
      VioGetCurType((PVIOCURSORINFO) cursor_type,(HVIO) 0);
      return;
    }

static void set_cursor_position(cursor_row,cursor_column)
  USHORT cursor_row;
  USHORT cursor_column;
    {
      VioSetCurPos(cursor_row,cursor_column,(HVIO) 0);
      return;
    }

static void set_cursor_type(cursor_type)
  VIOCURSORINFO *cursor_type;
    {
      VioSetCurType((PVIOCURSORINFO) cursor_type,(HVIO) 0);
      return;
    }

static void titillate()
    {
      set_cursor_position(cursor_row,cursor_column);
      titillator_index++;
      if (titillator_index > 3)
        titillator_index=0;
      putchar((int) titillator[titillator_index]);
      return;
    }

static int memory_allocated(num_primes,x_prime,y_prime,
 z_prime,x_division_index,y_division_index,color,base_z)
  long               num_primes;
  float huge         **x_prime;
  float huge         **y_prime;
  float huge         **z_prime;
  int   huge         **x_division_index;
  int   huge         **y_division_index;
  unsigned char huge **color;
  unsigned char huge **base_z;
    {
      static int  result;

      result
       =((*x_prime=(float huge *) halloc(num_primes,sizeof(float))) != NULL);
      if (result)
        {
          if (! (result=((*y_prime
           =(float huge *) halloc(num_primes,sizeof(float))) != NULL)))
            hfree((void huge *) *x_prime);
        }
      if (result)
        {
          if (! (result=((*z_prime
           =(float huge *) halloc(num_primes,sizeof(float))) != NULL)))
            {
              hfree((void huge *) *y_prime);
              hfree((void huge *) *x_prime);
            }
        }
      if (result)
        {
          if (! (result=((*x_division_index
           =(int huge *) halloc(num_primes,sizeof(int))) != NULL)))
            {
              hfree((void huge *) *z_prime);
              hfree((void huge *) *y_prime);
              hfree((void huge *) *x_prime);
            }
        }
      if (result)
        {
          if (! (result=((*y_division_index
           =(int huge *) halloc(num_primes,sizeof(int))) != NULL)))
            {
              hfree((void huge *) *x_division_index);
              hfree((void huge *) *z_prime);
              hfree((void huge *) *y_prime);
              hfree((void huge *) *x_prime);
            }
        }
      if (result)
        {
          if (! (result=((*color=(unsigned char huge *) 
           halloc(num_primes,sizeof(unsigned char))) != NULL)))
            {
              hfree((void huge *) *y_division_index);
              hfree((void huge *) *x_division_index);
              hfree((void huge *) *z_prime);
              hfree((void huge *) *y_prime);
              hfree((void huge *) *x_prime);
            }
        }
      if (result)
        {
          if (! (result=((*base_z=(unsigned char huge *) 
           halloc(num_primes,sizeof(unsigned char))) != NULL)))
            {
              hfree((void huge *) *color);
              hfree((void huge *) *y_division_index);
              hfree((void huge *) *x_division_index);
              hfree((void huge *) *z_prime);
              hfree((void huge *) *y_prime);
              hfree((void huge *) *x_prime);
            }
        }
      return(result);
    }

static void generate_maze()
    {
      static   int  counter_0;
      static   int  counter_1;
      static   int  counter_2;
      static   int  counter_3;
      static   int  counter_4;
      static   int  counter_5;
      static   int  counter_6;
      static   int  counter_7;
      static   int  delta_index_1a;
      static   int  delta_index_1b;
      static   int  delta_index_1c;
      static   int  delta_index_1d;
      static   int  delta_index_2;
      static   int  digit;
      static   int  digit_num;
      static   char seed [256];
      static   int  seed_length;
      static   int  sum;
      register int  x_out;
      register int  y_out;

      printf("\n     Random number seed?  ");
      gets(&seed[0]);
      get_cursor(&cursor_row,&cursor_column,&initial_cursor_type);
      memcpy((void *) &titillator_cursor_type,
       (const void *) &initial_cursor_type,sizeof(VIOCURSORINFO));
      titillator_cursor_type.attr=0xffff;
      set_cursor_type(&titillator_cursor_type);
      titillator_index=0;
      seed_length=strlen(&seed[0]);
      for (r_n_index_1=0; r_n_index_1 < seed_length; ++r_n_index_1)
        r_n[r_n_index_1]=(int) (seed[r_n_index_1] % 10);
      r_n_index_2=7;
      while (r_n_index_1 > 0)
        {
           r_n_index_1--;
           r_n[r_n_index_2]=r_n[r_n_index_1];
           r_n_index_2--;
        }
      while (r_n_index_2 >= 0)
        {
          r_n[r_n_index_2]=0;
          r_n_index_2--;
        }
      counter_0=r_n[1];
      counter_1=r_n[2];
      counter_2=r_n[3];
      counter_3=r_n[4];
      counter_4=r_n[5];
      counter_5=r_n[6];
      counter_6=r_n[7];
      counter_7=r_n[8];
      hash(&counter_0,&counter_1,&counter_2,&counter_3,&counter_4,&counter_5,
       &counter_6,&counter_7);
      delta_x[0][0]=-1;
      delta_y[0][0]=0;
      delta_x[1][0]=0;
      delta_y[1][0]=1;
      delta_x[2][0]=1;
      delta_y[2][0]=0;
      delta_x[3][0]=0;
      delta_y[3][0]=-1;
      delta_index_2=0;
      for (delta_index_1a=0; delta_index_1a < 4; ++delta_index_1a)
        for (delta_index_1b=0; delta_index_1b < 4; ++delta_index_1b)
          if (delta_index_1a != delta_index_1b)
            for (delta_index_1c=0; delta_index_1c < 4; ++delta_index_1c)
              if ((delta_index_1a != delta_index_1c)
              &&  (delta_index_1b != delta_index_1c))
                for (delta_index_1d=0; delta_index_1d < 4; ++delta_index_1d)
                  if ((delta_index_1a != delta_index_1d)
                  &&  (delta_index_1b != delta_index_1d)
                  &&  (delta_index_1c != delta_index_1d))
                    {
                      delta_x[delta_index_1a][delta_index_2]=delta_x[0][0];
                      delta_y[delta_index_1a][delta_index_2]=delta_y[0][0];
                      delta_x[delta_index_1b][delta_index_2]=delta_x[1][0];
                      delta_y[delta_index_1b][delta_index_2]=delta_y[1][0];
                      delta_x[delta_index_1c][delta_index_2]=delta_x[2][0];
                      delta_y[delta_index_1c][delta_index_2]=delta_y[2][0];
                      delta_x[delta_index_1d][delta_index_2]=delta_x[3][0];
                      delta_y[delta_index_1d][delta_index_2]=delta_y[3][0];
                      delta_index_2++;
                    };
      do
        {
          titillate();
          for (y_out=0; y_out <= MAX_Y; ++y_out)
            for (x_out=0; x_out <= MAX_X; ++x_out)
              page[y_out][x_out]='W';
          r_n[1]=counter_0+1;
          r_n[2]=counter_1+1;
          r_n[3]=counter_2+1;
          r_n[4]=counter_3+1;
          r_n[5]=counter_4+1;
          r_n[6]=counter_5+1;
          r_n[7]=counter_6+1;
          r_n[8]=counter_7+1;
          sum=0;
          for (digit_num=1; digit_num <= 3; ++digit_num)
            {
              digit=r_n[0];
              r_n_index_1=0;
              for (r_n_index_2=1; r_n_index_2 < 8; ++r_n_index_2)
                {
                  tem_int=r_n[r_n_index_2];
                  r_n[r_n_index_1]=tem_int;
                  digit+=tem_int;
                  if (digit >= 29)
                     digit-=29;
                  r_n_index_1=r_n_index_2;
                }
              r_n[7]=digit;
              sum=29*sum+digit;
            }
          x_maze=2*(sum % NUM_COLUMNS)+1;
          sum=0;
          for (digit_num=1; digit_num <= 3; ++digit_num)
            {
              digit=r_n[0];
              r_n_index_1=0;
              for (r_n_index_2=1; r_n_index_2 < 8; ++r_n_index_2)
                {
                  tem_int=r_n[r_n_index_2];
                  r_n[r_n_index_1]=tem_int;
                  digit+=tem_int;
                  if (digit >= 29)
                     digit-=29;
                  r_n_index_1=r_n_index_2;
                }
              r_n[7]=digit;
              sum=29*sum+digit;
            }
          y_maze=2*(sum % NUM_ROWS)+1;
          add_room();
          page[0][1]=' ';
          page[MAX_Y][MAX_X-1]=' ';
          increment(&counter_0,&counter_1,&counter_2,&counter_3,&counter_4,
           &counter_5,&counter_6,&counter_7);
        }
      while (3*num_rooms_in_solution() < NUM_ROOMS_IN_MAZE);
      return;
    }

static int substitution_high [100] =
             { 4,1,2,8,8,9,9,6,5,7,2,1,2,9,8,8,6,3,5,1,9,5,4,4,9,8,6,0,8,0,
               6,0,2,4,1,9,2,0,7,4,7,3,0,0,2,6,8,9,4,0,8,3,2,3,2,5,2,4,6,9,
               7,9,1,3,5,7,1,1,4,5,8,1,6,0,5,7,8,2,3,3,7,3,5,1,7,5,4,0,3,6,
               3,7,7,1,9,4,0,5,6,6 
             };
static int substitution_low [100] =
             { 1,2,2,1,5,5,4,6,4,6,4,4,5,6,6,3,0,9,6,5,7,2,0,9,3,4,2,3,9,1,
               9,9,9,3,8,9,3,4,1,5,0,5,2,7,0,8,8,0,4,5,0,3,6,8,1,7,8,8,7,1,
               3,2,7,7,1,8,0,3,7,5,2,6,4,0,9,9,7,7,4,6,2,0,0,1,7,3,6,6,1,1,
               2,4,5,9,8,2,8,8,3,5 
             };
static void hash(counter_0,counter_1,counter_2,counter_3,counter_4,counter_5,
 counter_6,counter_7)
  int *counter_0;
  int *counter_1;
  int *counter_2;
  int *counter_3;
  int *counter_4;
  int *counter_5;
  int *counter_6;
  int *counter_7;
    {
      register int iteration;
      static   int seed_0;
      static   int seed_1;
      static   int seed_2;
      static   int seed_3;
      static   int seed_4;
      static   int seed_5;
      static   int seed_6;
      static   int seed_7;
      register int substitution_index;
      static   int tem_0;
      static   int tem_1;
      static   int tem_2;

      seed_0=(*counter_0);
      seed_1=(*counter_1);
      seed_2=(*counter_2);
      seed_3=(*counter_3);
      seed_4=(*counter_4);
      seed_5=(*counter_5);
      seed_6=(*counter_6);
      seed_7=(*counter_7);
      for (iteration=1; iteration <= 8; iteration++)
        {
          substitution_index=10*seed_1+seed_0;
          tem_0=substitution_low[substitution_index];
          tem_1=substitution_high[substitution_index];
          substitution_index=10*seed_3+seed_2;
          seed_0=substitution_low[substitution_index];
          tem_2=substitution_high[substitution_index];
          substitution_index=10*seed_5+seed_4;
          seed_2=substitution_low[substitution_index];
          seed_1=substitution_high[substitution_index];
          substitution_index=10*seed_7+seed_6;
          seed_5=substitution_low[substitution_index];
          seed_7=substitution_high[substitution_index];
          seed_3=tem_0;
          seed_6=tem_1;
          seed_4=tem_2;
        }
      (*counter_0)=seed_0;
      (*counter_1)=seed_1;
      (*counter_2)=seed_2;
      (*counter_3)=seed_3;
      (*counter_4)=seed_4;
      (*counter_5)=seed_5;
      (*counter_6)=seed_6;
      (*counter_7)=seed_7;
      return;
    }

static void increment(counter_0,counter_1,counter_2,counter_3,counter_4,
 counter_5,counter_6,counter_7)
  int *counter_0;
  int *counter_1;
  int *counter_2;
  int *counter_3;
  int *counter_4;
  int *counter_5;
  int *counter_6;
  int *counter_7;
    {
      register tem;

      tem=(*counter_0)+1;
      if (tem <= 9)
        (*counter_0)=tem;
      else
        {
          (*counter_0)=0;
          tem=(*counter_1)+1;
          if (tem <= 9)
            (*counter_1)=tem;
          else
            {
              (*counter_1)=0;
              tem=(*counter_2)+1;
              if (tem <= 9)
                (*counter_2)=tem;
              else
                {
                  (*counter_2)=0;
                  tem=(*counter_3)+1;
                  if (tem <= 9)
                    (*counter_3)=tem;
                  else
                    {
                      (*counter_3)=0;
                      tem=(*counter_4)+1;
                      if (tem <= 9)
                        (*counter_4)=tem;
                      else
                        {
                          (*counter_4)=0;
                          tem=(*counter_5)+1;
                          if (tem <= 9)
                            (*counter_5)=tem;
                          else
                            {
                              (*counter_5)=0;
                              tem=(*counter_6)+1;
                              if (tem <= 9)
                                (*counter_6)=tem;
                              else
                                {
                                  (*counter_6)=0;
                                  tem=(*counter_7)+1;
                                  if (tem <= 9)
                                    (*counter_7)=tem;
                                  else
                                    (*counter_7)=0;
                                }
                            }
                        }
                    }
                }
            }
        }
      return;
    }
 
static int num_rooms_in_solution()
    {
      int direction_x;
      int direction_y;
      int initial_direction_x;
      int initial_direction_y;
      int passage_found;
      int result;
      int tem;
      int x;
      int x_next;
      int y;
      int y_next;

      result=1;
      x=1;
      y=1;
      page[y][x]='S';
      initial_direction_x=0;
      initial_direction_y=1;
      do
        {
          passage_found=FALSE;
          direction_x=-initial_direction_y;
          direction_y=initial_direction_x;
          while (! passage_found)
            {
              x_next=x+direction_x;
              y_next=y+direction_y;
              if (page[y_next][x_next] != 'W')
                passage_found=TRUE;
              else
                {
                  tem=direction_x;
                  direction_x=direction_y;
                  direction_y=-tem;
                }
            };
          if (page[y_next][x_next] == ' ')
            {
              result++;
              page[y_next][x_next]='S';
              x=x_next+direction_x;
              y=y_next+direction_y;
              page[y][x]='S';
            }
          else
            {
              result--;
              page[y][x]=' ';
              page[y_next][x_next]=' ';
              x=x_next+direction_x;
              y=y_next+direction_y;
            };
          initial_direction_x=direction_x;
          initial_direction_y=direction_y;
        }
      while ((x != MAX_X_LESS_1) || (y != MAX_Y_LESS_1));
      return(result);
    }

static void add_room()
    {
      unsigned char delta_index_1;
      unsigned char delta_index_2;

      page[y_maze][x_maze]=' ';
      delta_index_1=0;
      do
        {
          delta_index_2=(unsigned char) r_n[0];
          r_n_index_1=0;
          for (r_n_index_2=1; r_n_index_2 < 8; ++r_n_index_2)
            {
              tem_int=r_n[r_n_index_2];
              r_n[r_n_index_1]=tem_int;
              delta_index_2+=(unsigned char) tem_int;
              if (delta_index_2 >= 29)
                delta_index_2-=29;
              r_n_index_1=r_n_index_2;
            }
          r_n[7]=delta_index_2;
        }
      while (delta_index_2 >= 24);
      while (delta_index_1 < 4)
        {
          x_next=x_maze+2*delta_x[delta_index_1][delta_index_2];
          if ((x_next <= 0) || (x_next >= MAX_X))
            delta_index_1++;
          else
            {
              y_next=y_maze+2*delta_y[delta_index_1][delta_index_2];
              if ((y_next <= 0) || (y_next >= MAX_Y))
                delta_index_1++;
              else
                if (page[y_next][x_next] == 'W')
                  {
                    if (x_maze == x_next)
                      {
                        y_wall=(y_maze+y_next)/2;
                        page[y_wall][x_next]=' ';
                      }
                    else
                      {
                        x_wall=(x_maze+x_next)/2;
                        page[y_next][x_wall]=' ';
                      }
                    x_maze=x_next;
                    y_maze=y_next;
                    add_room();
                    x_maze-=2*delta_x[delta_index_1][delta_index_2];
                    y_maze-=2*delta_y[delta_index_1][delta_index_2];
                  }
                else
                  delta_index_1++;
            }
        }
    }

static void evaluate_and_transform(x_min,x_max,y_min,y_max,num_x_divisions,
 num_y_divisions,rotation,tilt,x_prime,y_prime,z_prime,x_prime_max,y_prime_min,
 y_prime_max,z_prime_min,z_prime_max,light,light_prime,x_division_index,
 y_division_index,base_z)
  double             x_min;
  double             x_max;
  double             y_min;
  double             y_max;
  int                num_x_divisions;
  int                num_y_divisions;
  double             rotation;
  double             tilt;
  float huge         *x_prime;
  float huge         *y_prime;
  float huge         *z_prime;
  double             *x_prime_max;
  double             *y_prime_min;
  double             *y_prime_max;
  double             *z_prime_min;
  double             *z_prime_max;
  vertex_rec         *light;
  vertex_rec         *light_prime;
  int huge           *x_division_index;
  int huge           *y_division_index;
  unsigned char huge *base_z;
    {
      static   double cos_rotation;
      static   double cos_tilt;
      static   double magnitude;
      static   long   prime_num;
      static   double radians;
      static   double radians_per_degree;
      static   double sin_rotation;
      static   double sin_tilt;
      static   double x;
      static   double x_delta;
      register int    x_division_num;
      static   double x_rotated;
      static   double y;
      static   double y_delta;
      register int    y_division_num;
      static   double z;

      radians_per_degree=atan(1.0)/45.0;
      radians=tilt*radians_per_degree;
      cos_tilt=cos(radians);
      sin_tilt=sin(radians);
      radians=rotation*radians_per_degree;
      cos_rotation=cos(radians);
      sin_rotation=sin(radians);
      z=fabs(f(x_min,y_min));
      x_rotated=x_min*cos_rotation+y_min*sin_rotation;
      *y_prime_min=-x_min*sin_rotation+y_min*cos_rotation;
      *z_prime_min=-x_rotated*sin_tilt+z*cos_tilt;
      *y_prime_max=*y_prime_min;
      *z_prime_max=*z_prime_min;
      *x_prime_max=x_rotated*cos_tilt+z*sin_tilt;
      x_delta=(double) (num_x_divisions-1);
      x_delta=(x_max-x_min)/x_delta;
      y_delta=(double) (num_y_divisions-1);
      y_delta=(y_max-y_min)/y_delta;
      x=x_min;
      prime_num=0l;
      for (x_division_num=0; x_division_num < num_x_divisions; x_division_num++)
        {
          titillate();
          y=y_min;
          for (y_division_num=0; y_division_num < num_y_divisions;
           y_division_num++)
            {
              z=f(x,y);
              if (z > 0.0)
                base_z[prime_num]=(unsigned char) 1;
              else
                if (z < 0.0)
                  base_z[prime_num]=(unsigned char) 2;
                else
                  base_z[prime_num]=(unsigned char) 0;
              z=fabs(z);
              x_division_index[prime_num]=x_division_num;
              y_division_index[prime_num]=y_division_num;
              x_rotated=x*cos_rotation+y*sin_rotation;
              y_prime[prime_num]=(float) (-x*sin_rotation+y*cos_rotation);
              x_prime[prime_num]=(float) (x_rotated*cos_tilt+z*sin_tilt);
              z_prime[prime_num]=(float) (-x_rotated*sin_tilt+z*cos_tilt);
              if (((double) (x_prime[prime_num])) > *x_prime_max)
                *x_prime_max=(double) (x_prime[prime_num]);
              if (((double) (y_prime[prime_num])) < *y_prime_min)
                *y_prime_min=(double) (y_prime[prime_num]);
              if (((double) (y_prime[prime_num])) > *y_prime_max)
                *y_prime_max=(double) (y_prime[prime_num]);
              if (((double) (z_prime[prime_num])) < *z_prime_min)
                *z_prime_min=(double) (z_prime[prime_num]);
              if (((double) (z_prime[prime_num])) > *z_prime_max)
                *z_prime_max=(double) (z_prime[prime_num]);
              y+=y_delta;
              prime_num++;
            }
          x+=x_delta;
        }
      magnitude=(*light).x*(*light).x;
      magnitude+=((*light).y*(*light).y);
      magnitude+=((*light).z*(*light).z);
      magnitude=sqrt(magnitude);
      (*light).x/=magnitude;
      (*light).y/=magnitude;
      (*light).z/=magnitude;
      /* lighting doesn't change with tilt or rotation */
      x_rotated=(*light).x*cos_rotation+(*light).y*sin_rotation;
      (*light_prime).y=-(*light).x*sin_rotation+(*light).y*cos_rotation;
      (*light_prime).z=-x_rotated*sin_tilt+(*light).z*cos_tilt;
      (*light_prime).x=x_rotated*cos_tilt+(*light).z*sin_tilt;
      return;
    }

static void shade(num_x_divisions,num_y_divisions,x_prime,y_prime,z_prime,color,
 light_prime)
  int                num_x_divisions;
  int                num_y_divisions;
  float huge         *x_prime;
  float huge         *y_prime;
  float huge         *z_prime;
  unsigned char huge *color;
  vertex_rec         *light_prime;
    {
      static   double     magnitude;
      static   vertex_rec normal;
      static   long       prime_num;
      static   vertex_rec vertex [4];
      register int        x_division_num;
      register int        y_division_num;

      prime_num=0l;
      for (x_division_num=0; x_division_num < num_x_divisions;
       x_division_num++)
        {
          titillate();
          for (y_division_num=0; y_division_num < num_y_divisions;
           y_division_num++)
            {
              vertex[0].x=(double) (x_prime[prime_num]);
              vertex[0].y=(double) (y_prime[prime_num]);
              vertex[0].z=(double) (z_prime[prime_num]);
              if (x_division_num < (num_x_divisions-1))
                if (y_division_num < (num_y_divisions-1))
                  {
                    prime_num+=((long) num_y_divisions);
                    vertex[1].x=(double) (x_prime[prime_num]);
                    vertex[1].y=(double) (y_prime[prime_num]);
                    vertex[1].z=(double) (z_prime[prime_num]);
                    prime_num++;
                    vertex[2].x=(double) (x_prime[prime_num]);
                    vertex[2].y=(double) (y_prime[prime_num]);
                    vertex[2].z=(double) (z_prime[prime_num]);
                    prime_num-=((long) num_y_divisions);
                    vertex[3].x=(double) (x_prime[prime_num]);
                    vertex[3].y=(double) (y_prime[prime_num]);
                    vertex[3].z=(double) (z_prime[prime_num]);
                    prime_num--;
                  }
                else
                  {
                    prime_num--;
                    vertex[1].x=(double) (x_prime[prime_num]);
                    vertex[1].y=(double) (y_prime[prime_num]);
                    vertex[1].z=(double) (z_prime[prime_num]);
                    prime_num+=((long) num_y_divisions);
                    vertex[2].x=(double) (x_prime[prime_num]);
                    vertex[2].y=(double) (y_prime[prime_num]);
                    vertex[2].z=(double) (z_prime[prime_num]);
                    prime_num++;
                    vertex[3].x=(double) (x_prime[prime_num]);
                    vertex[3].y=(double) (y_prime[prime_num]);
                    vertex[3].z=(double) (z_prime[prime_num]);
                    prime_num-=((long) num_y_divisions);
                  }
              else
                if (y_division_num < (num_y_divisions-1))
                  {
                    prime_num++;
                    vertex[1].x=(double) (x_prime[prime_num]);
                    vertex[1].y=(double) (y_prime[prime_num]);
                    vertex[1].z=(double) (z_prime[prime_num]);
                    prime_num-=((long) num_y_divisions);
                    vertex[2].x=(double) (x_prime[prime_num]);
                    vertex[2].y=(double) (y_prime[prime_num]);
                    vertex[2].z=(double) (z_prime[prime_num]);
                    prime_num--;
                    vertex[3].x=(double) (x_prime[prime_num]);
                    vertex[3].y=(double) (y_prime[prime_num]);
                    vertex[3].z=(double) (z_prime[prime_num]);
                    prime_num+=((long) num_y_divisions);
                  }
                else
                  {
                    prime_num-=((long) num_y_divisions);
                    vertex[1].x=(double) (x_prime[prime_num]);
                    vertex[1].y=(double) (y_prime[prime_num]);
                    vertex[1].z=(double) (z_prime[prime_num]);
                    prime_num--;
                    vertex[2].x=(double) (x_prime[prime_num]);
                    vertex[2].y=(double) (y_prime[prime_num]);
                    vertex[2].z=(double) (z_prime[prime_num]);
                    prime_num+=((long) num_y_divisions);
                    vertex[3].x=(double) (x_prime[prime_num]);
                    vertex[3].y=(double) (y_prime[prime_num]);
                    vertex[3].z=(double) (z_prime[prime_num]);
                    prime_num++;
                  }
              normal.x
               =(vertex[1].y-vertex[0].y)*(vertex[3].z-vertex[0].z)
               -(vertex[3].y-vertex[0].y)*(vertex[1].z-vertex[0].z)
               +(vertex[2].y-vertex[1].y)*(vertex[0].z-vertex[1].z)
               -(vertex[0].y-vertex[1].y)*(vertex[2].z-vertex[1].z)
               +(vertex[3].y-vertex[2].y)*(vertex[1].z-vertex[2].z)
               -(vertex[1].y-vertex[2].y)*(vertex[3].z-vertex[2].z)
               +(vertex[0].y-vertex[3].y)*(vertex[2].z-vertex[3].z)
               -(vertex[2].y-vertex[3].y)*(vertex[0].z-vertex[3].z);
              normal.y
               =(vertex[3].x-vertex[0].x)*(vertex[1].z-vertex[0].z)
               -(vertex[1].x-vertex[0].x)*(vertex[3].z-vertex[0].z)
               +(vertex[0].x-vertex[1].x)*(vertex[2].z-vertex[1].z)
               -(vertex[2].x-vertex[1].x)*(vertex[0].z-vertex[1].z)
               +(vertex[1].x-vertex[2].x)*(vertex[3].z-vertex[2].z)
               -(vertex[3].x-vertex[2].x)*(vertex[1].z-vertex[2].z)
               +(vertex[2].x-vertex[3].x)*(vertex[0].z-vertex[3].z)
               -(vertex[0].x-vertex[3].x)*(vertex[2].z-vertex[3].z);
              normal.z
               =(vertex[1].x-vertex[0].x)*(vertex[3].y-vertex[0].y)
               -(vertex[3].x-vertex[0].x)*(vertex[1].y-vertex[0].y)
               +(vertex[2].x-vertex[1].x)*(vertex[0].y-vertex[1].y)
               -(vertex[0].x-vertex[1].x)*(vertex[2].y-vertex[1].y)
               +(vertex[3].x-vertex[2].x)*(vertex[1].y-vertex[2].y)
               -(vertex[1].x-vertex[2].x)*(vertex[3].y-vertex[2].y)
               +(vertex[0].x-vertex[3].x)*(vertex[2].y-vertex[3].y)
               -(vertex[2].x-vertex[3].x)*(vertex[0].y-vertex[3].y);
              if (normal.x < 0.0)
                color[prime_num]=NUM_COLORS;
              else
                {
                  magnitude
                   =sqrt(normal.x*normal.x+normal.y*normal.y+normal.z*normal.z);
                  if (magnitude == 0.0)
                    color[prime_num]=(unsigned char) 0;
                  else
                    {
                      color[prime_num]
                       =(unsigned char) ((((float) (NUM_COLORS-1))/2.0)*(1.0
                       +((*light_prime).x*normal.x+(*light_prime).y*normal.y
                       +(*light_prime).z*normal.z)/magnitude));
                      if (color[prime_num] >= (unsigned char) (NUM_COLORS-1))
                        color[prime_num]=(unsigned char) (NUM_COLORS-2);
                    }
                }
              prime_num++;
            }
        }
      return;
    }

static void adjust_perspective(num_x_divisions,num_y_divisions,x_prime,y_prime,
 z_prime,x_prime_max,y_prime_min,y_prime_max,z_prime_min,z_prime_max)
  int        num_x_divisions;
  int        num_y_divisions;
  float huge *x_prime;
  float huge *y_prime;
  float huge *z_prime;
  double     x_prime_max;
  double     y_prime_min;
  double     y_prime_max;
  double     z_prime_min;
  double     z_prime_max;  
    {
      static   long       prime_num;
      static   vertex_rec vertex [4];
      register int        x_division_num;
      static   double     x_eye;
      static   double     y_center;
      register int        y_division_num;
      static   double     z_center;

      if ((y_prime_max-y_prime_min) > (z_prime_max-z_prime_min))
        x_eye=1.1*(y_prime_max-y_prime_min)+x_prime_max;
      else
        x_eye=1.1*(z_prime_max-z_prime_min)+x_prime_max;
      if (((y_prime_max-y_prime_min) > (z_prime_max-z_prime_min))
      ||  (z_prime_max != z_prime_min))
        {
          y_center=(y_prime_max+y_prime_min)/2.0;
          z_center=(z_prime_max+z_prime_min)/2.0;
          prime_num=0l;
          for (x_division_num=0; x_division_num < num_x_divisions;
           x_division_num++)
            {
              titillate();
              for (y_division_num=0; y_division_num < num_y_divisions;
               y_division_num++)
                {
                  vertex[0].x=(double) (x_prime[prime_num]);
                  vertex[0].y=(double) (y_prime[prime_num]);
                  vertex[0].z=(double) (z_prime[prime_num]);
                  if (x_division_num < (num_x_divisions-1))
                    if (y_division_num < (num_y_divisions-1))
                      {
                        prime_num+=((long) num_y_divisions);
                        vertex[1].x=(double) (x_prime[prime_num]);
                        vertex[1].y=(double) (y_prime[prime_num]);
                        vertex[1].z=(double) (z_prime[prime_num]);
                        prime_num++;
                        vertex[2].x=(double) (x_prime[prime_num]);
                        vertex[2].y=(double) (y_prime[prime_num]);
                        vertex[2].z=(double) (z_prime[prime_num]);
                        prime_num-=((long) num_y_divisions);
                        vertex[3].x=(double) (x_prime[prime_num]);
                        vertex[3].y=(double) (y_prime[prime_num]);
                        vertex[3].z=(double) (z_prime[prime_num]);
                        prime_num--;
                      }
                    else
                      {
                        prime_num--;
                        vertex[1].x=(double) (x_prime[prime_num]);
                        vertex[1].y=(double) (y_prime[prime_num]);
                        vertex[1].z=(double) (z_prime[prime_num]);
                        prime_num+=((long) num_y_divisions);
                        vertex[2].x=(double) (x_prime[prime_num]);
                        vertex[2].y=(double) (y_prime[prime_num]);
                        vertex[2].z=(double) (z_prime[prime_num]);
                        prime_num++;
                        vertex[3].x=(double) (x_prime[prime_num]);
                        vertex[3].y=(double) (y_prime[prime_num]);
                        vertex[3].z=(double) (z_prime[prime_num]);
                        prime_num-=((long) num_y_divisions);
                      }
                  else
                    if (y_division_num < (num_y_divisions-1))
                      {
                        prime_num++;
                        vertex[1].x=(double) (x_prime[prime_num]);
                        vertex[1].y=(double) (y_prime[prime_num]);
                        vertex[1].z=(double) (z_prime[prime_num]);
                        prime_num-=((long) num_y_divisions);
                        vertex[2].x=(double) (x_prime[prime_num]);
                        vertex[2].y=(double) (y_prime[prime_num]);
                        vertex[2].z=(double) (z_prime[prime_num]);
                        prime_num--;
                        vertex[3].x=(double) (x_prime[prime_num]);
                        vertex[3].y=(double) (y_prime[prime_num]);
                        vertex[3].z=(double) (z_prime[prime_num]);
                        prime_num+=((long) num_y_divisions);
                      }
                    else
                      {
                        prime_num-=((long) num_y_divisions);
                        vertex[1].x=(double) (x_prime[prime_num]);
                        vertex[1].y=(double) (y_prime[prime_num]);
                        vertex[1].z=(double) (z_prime[prime_num]);
                        prime_num--;
                        vertex[2].x=(double) (x_prime[prime_num]);
                        vertex[2].y=(double) (y_prime[prime_num]);
                        vertex[2].z=(double) (z_prime[prime_num]);
                        prime_num+=((long) num_y_divisions);
                        vertex[3].x=(double) (x_prime[prime_num]);
                        vertex[3].y=(double) (y_prime[prime_num]);
                        vertex[3].z=(double) (z_prime[prime_num]);
                        prime_num++;
                      }
                  y_prime[prime_num]=(float) y_center
                   +(vertex[0].y-y_center)*(x_eye-x_prime_max)
                   /(x_eye-vertex[0].x);
                  z_prime[prime_num]=(float) z_center
                   +(vertex[0].z-z_center)*(x_eye-x_prime_max)
                   /(x_eye-vertex[0].x);
                  x_prime[prime_num]=(float)
                   (-(vertex[0].x+vertex[1].x+vertex[2].x+vertex[3].x)/4.0);
                  prime_num++;
                }
            }
         }
      return;
    }

static void sort_back_to_front(num_primes,x_prime,x_division_index,
 y_division_index)
  long       num_primes;
  float huge *x_prime;
  int huge   *x_division_index;
  int huge   *y_division_index;
    {
      static   int   finished;
      static   long  key_index_1;
      static   long  key_index_2;
      static   long  left;
      static   long  right;
      static   float t1;
      register int   t2;
      register int   t3;

      left=num_primes/((long) 2);
      right=num_primes-1l;
      t1=x_prime[0];
      t2=x_division_index[0];
      t3=y_division_index[0];
      while (right > 0l)
        {
          titillate();
          if (left > 0l)
            {
              left--;
              t1=x_prime[left];
              t2=x_division_index[left];
              t3=y_division_index[left];
            }
          else
            {
              t1=x_prime[right];
              t2=x_division_index[right];
              t3=y_division_index[right];
              x_prime[right]=x_prime[0];
              x_division_index[right]=x_division_index[0];
              y_division_index[right]=y_division_index[0];
              right--;
            }
          if (right > 0l)
            {
              finished=FALSE;
              key_index_2=left;
              while (! finished)
                {
                  key_index_1=key_index_2;
                  key_index_2+=key_index_2;
                  key_index_2++;
                  if (key_index_2 > right)
                    finished=TRUE;
                  else
                    {
                      if (key_index_2 != right)
                        {
                          if (x_prime[key_index_2] > x_prime[key_index_2+1])
                            key_index_2++;
                        }
                      if (t1 <= x_prime[key_index_2])
                        finished=TRUE;
                      else
                        {
                          x_prime[key_index_1]=x_prime[key_index_2];
                          x_division_index[key_index_1]
                           =x_division_index[key_index_2];
                          y_division_index[key_index_1]
                           =y_division_index[key_index_2];
                        }
                    }
                }
              x_prime[key_index_1]=t1;
              x_division_index[key_index_1]=t2;
              y_division_index[key_index_1]=t3;
            }
        }
      x_prime[0]=t1;
      x_division_index[0]=t2;
      y_division_index[0]=t3;
      return;
    }

static void plot(num_x_divisions,x_division_index,num_y_divisions,
 y_division_index,num_primes,y_prime,z_prime,y_prime_min,y_prime_max,z_prime_min,
 z_prime_max,color,base_z,solve)
  int                num_x_divisions;
  int huge           *x_division_index;
  int                num_y_divisions;
  int huge           *y_division_index;
  long               num_primes;
  float huge         *y_prime;
  float huge         *z_prime;
  double             y_prime_min;
  double             y_prime_max;
  double             z_prime_min;
  double             z_prime_max;
  unsigned char huge *color;
  unsigned char huge *base_z;
  int                solve;
    {  
      static   double        aspect_ratio;
      static   double        box_delta_x;
      static   double        box_delta_y;
      static   box_rec       box [4];
      static   int           box_num_1;
      static   int           box_num_2;
      static   double        box_x_intercept;
      static   int           box_x1;
      static   int           box_x2;
      static   int           box_y_max;
      static   int           box_y_min;
      static   double        box_y_offset;
      static   int           box_y1;
      static   short         color_num;
      static   int           intercept_count_mod_2;
      register int           line_x1;
      register int           line_x2;
      static   double        pixels_per_unit;
      static   long          prime_num;
      static   int           solution;
      static   vertex_rec    vertex [4];
      static   int           x_division_num;
      static   long          x_prime_num;
      static   int           y_division_num;
      static   double        y_offset;
      static   double        y_out_max;
      static   double        z_offset;
      static   double        z_out_max;

      aspect_ratio=(HEIGHT_OF_SCREEN/WIDTH_OF_SCREEN)
       /(((double) NUM_Y_PIXELS)/((double) NUM_X_PIXELS));
      y_out_max=(double) (NUM_X_PIXELS-1);
      z_out_max=(double) (NUM_Y_PIXELS-1);
      if (aspect_ratio*z_out_max*(y_prime_max-y_prime_min)
       > y_out_max*(z_prime_max-z_prime_min))
        {
          pixels_per_unit
           =y_out_max/(aspect_ratio*(y_prime_max-y_prime_min));
          y_offset=0.0;
          z_offset
           =-(z_out_max-pixels_per_unit*(z_prime_max-z_prime_min))/2.0;
        }
      else
        if (aspect_ratio*z_out_max*(y_prime_max-y_prime_min)
         < y_out_max*(z_prime_max-z_prime_min))
          {
            pixels_per_unit=z_out_max/(z_prime_max-z_prime_min);
            y_offset=(y_out_max
             -aspect_ratio*pixels_per_unit*(y_prime_max-y_prime_min))/2.0;
            z_offset=0.0;
          }
        else
          {
            pixels_per_unit=1.0;
            y_offset=y_out_max/2.0;
            z_offset=-z_out_max/2.0;
          };
      for (x_prime_num=0l; x_prime_num < num_primes; x_prime_num++)
        {
          x_division_num=x_division_index[x_prime_num];
          if (x_division_num < (num_x_divisions-1))
            {
              y_division_num=y_division_index[x_prime_num];
              if (y_division_num < (num_y_divisions-1))
                {
                  prime_num
                   =((long) num_y_divisions)*((long) x_division_num)
                   +((long) y_division_num);
                  color_num=(short) (color[prime_num]);
                  if (color_num < NUM_COLORS)
                    {
                      vertex[0].y=(double) (y_prime[prime_num]);
                      vertex[0].z=(double) (z_prime[prime_num]);
                      solution=(base_z[prime_num] == (unsigned char) 2);
                      prime_num+=((long) num_y_divisions);
                      vertex[1].y=(double) (y_prime[prime_num]);
                      vertex[1].z=(double) (z_prime[prime_num]);
                      if (solution)
                        solution=(base_z[prime_num] == (unsigned char) 2);
                      prime_num++;
                      vertex[2].y=(double) (y_prime[prime_num]);
                      vertex[2].z=(double) (z_prime[prime_num]);
                      if (solution)
                        solution=(base_z[prime_num] == (unsigned char) 2);
                      prime_num-=((long) num_y_divisions);
                      vertex[3].y=(double) (y_prime[prime_num]);
                      vertex[3].z=(double) (z_prime[prime_num]);
                      if (solution)
                        solution=(base_z[prime_num] == (unsigned char) 2);
                      if ((! solve) || (solution))
                        {
                          if (solve)
                            color_num=(short) (NUM_COLORS-1);
                          for (box_num_1=0; box_num_1 < 4; box_num_1++)
                            {
                              box[box_num_1].x=(int) (y_offset
                               +pixels_per_unit*aspect_ratio
                               *(vertex[box_num_1].y-y_prime_min));
                              box[box_num_1].y=(int) (z_offset+z_out_max
                               -pixels_per_unit
                               *(vertex[box_num_1].z-z_prime_min));
                            }
                          box_y_min=box[0].y;
                          box_y_max=box_y_min;
                          for (box_num_1=1; box_num_1 < 4; box_num_1++)
                            {
                              if (box[box_num_1].y < box_y_min)
                                box_y_min=box[box_num_1].y;
                              if (box[box_num_1].y > box_y_max)
                                box_y_max=box[box_num_1].y;
                            }
                          for (box_y1=box_y_min; box_y1 <= box_y_max; ++box_y1)
                            {
                              intercept_count_mod_2=0;
                              box_num_2=1;
                              for (box_num_1=0; box_num_1 < 4; ++box_num_1)
                                {
                                  if (box[box_num_1].y >= box_y1)
                                    {
                                      if (box_y1 > box[box_num_2].y)
                                        {
                                          box_delta_y=(double)
                                           (box[box_num_2].y-box[box_num_1].y);
                                          box_delta_x=(double)
                                           (box[box_num_2].x-box[box_num_1].x);
                                          box_y_offset=(double)
                                           (box_y1-box[box_num_1].y);
                                          box_x_intercept
                                           =(double) (box[box_num_1].x);
                                          box_x1
                                           =(int) ((box_delta_x*box_y_offset)
                                           /box_delta_y+box_x_intercept);
                                          if (intercept_count_mod_2 == 0)
                                            box_x2=box_x1;
                                          else
                                            {
                                              if (box_x1 < box_x2)
                                                {
                                                  line_x1=box_x1;
                                                  line_x2=box_x2;
                                                }
                                              else
                                                {
                                                  line_x1=box_x2;
                                                  line_x2=box_x1;
                                                }
                                              set_pixel(line_x1,box_y1,
                                               color_num);
                                              while (line_x1 < line_x2)
                                                {
                                                  line_x1++;
                                                  set_pixel(line_x1,box_y1,
                                                   color_num);
                                                }
                                            }
                                          intercept_count_mod_2
                                           =1-intercept_count_mod_2;
                                        }
                                    }
                                  else
                                    {
                                      if (box_y1 <= box[box_num_2].y)
                                        {
                                          box_delta_y=(double)
                                           (box[box_num_2].y-box[box_num_1].y);
                                          box_delta_x=(double)
                                           (box[box_num_2].x-box[box_num_1].x);
                                          box_y_offset=(double)
                                           (box_y1-box[box_num_1].y);
                                          box_x_intercept
                                           =(double) (box[box_num_1].x);
                                          box_x1
                                           =(int) ((box_delta_x*box_y_offset)
                                           /box_delta_y+box_x_intercept);
                                          if (intercept_count_mod_2 == 0)
                                            box_x2=box_x1;
                                          else
                                            {
                                              if (box_x1 < box_x2)
                                                {
                                                  line_x1=box_x1;
                                                  line_x2=box_x2;
                                                }
                                              else
                                                {
                                                  line_x1=box_x2;
                                                  line_x2=box_x1;
                                                }
                                              set_pixel(line_x1,box_y1,
                                               color_num);
                                              while (line_x1 < line_x2)
                                                {
                                                  line_x1++;
                                                  set_pixel(line_x1,box_y1,
                                                   color_num);
                                                }
                                            }
                                          intercept_count_mod_2
                                           =1-intercept_count_mod_2;
                                        }
                                    }
                                  box_num_2++;
                                  if (box_num_2 >= 4)
                                    box_num_2=0;
                                }
                            }
                        }
                    }
                }
            }
        }
      return;
    }

static double f(x,y)
  double x;
  double y;
    {
      static   int    solution;
      register int    x_next;
      static   int    x_offset;
      static   int    x_out;
      static   int    y_next;
      register int    y_offset;
      static   int    y_out;
      static   double z;

      y_out=(int) x;
      y_next=--y_out;
      y_out/=(2*RESOLUTION);
      if (4*(y_next-2*RESOLUTION*y_out) >= 5*RESOLUTION)
        y_out+=y_out;
      else
        {
          y_out+=y_out;
          y_out--;
        }
      if (y_out < 0)
        z=0.0;
      else
        if (y_out > MAX_Y)
          z=0.0;
        else
          {
            x_out=(int) y;
            x_next=--x_out;
            x_out/=(2*RESOLUTION);
            if (4*(x_next-2*RESOLUTION*x_out) >= 5*RESOLUTION)
              x_out+=x_out;
            else
              {
                x_out+=x_out;
                x_out--;
              }
            if (x_out < 0)
              z=0.0;
            else
              if (x_out > MAX_X)
                z=0.0;
              else
                if (page[y_out][x_out] == 'W')
                  {
                    solution=FALSE;
                    for (x_offset=-1; x_offset <= 1; x_offset++)
                      for (y_offset=-1; y_offset <= 1; y_offset++)
                        if (x_offset != 0)
                          {
                            x_next=x_out+x_offset;
                            y_next=y_out+y_offset;
                            if ((x_next >= 0)
                            &&  (x_next <= MAX_X)
                            &&  (y_next >= 0)
                            &&  (y_next <= MAX_Y)
                            &&  (page[y_next][x_next] == 'S'))
                              solution=TRUE;
                          }
                        else
                          {
                            if (y_offset != 0)
                              {
                                x_next=x_out+x_offset;
                                y_next=y_out+y_offset;
                                if ((x_next >= 0)
                                &&  (x_next <= MAX_X)
                                &&  (y_next >= 0)
                                &&  (y_next <= MAX_Y)
                                &&  (page[y_next][x_next] == 'S'))
                                  solution=TRUE;
                              }
                          };
                    z=15.0;
                    if (solution)
                      z=-z;
                  }
                else
                  z=0.0;

          }
      return(z);
    }

static void free_memory(x_prime,y_prime,z_prime,x_division_index,
 y_division_index,color,base_z)
  float huge         **x_prime;
  float huge         **y_prime;
  float huge         **z_prime;
  int   huge         **x_division_index;
  int   huge         **y_division_index;
  unsigned char huge **color;
  unsigned char huge **base_z;
    {
      hfree((void huge *) *base_z);
      hfree((void huge *) *color);
      hfree((void huge *) *y_division_index);
      hfree((void huge *) *x_division_index);
      hfree((void huge *) *z_prime);
      hfree((void huge *) *y_prime);
      hfree((void huge *) *x_prime);
      return;
    }

static int VGA_640_480_16()
  {
    static char          *buffer;
    static USHORT        cell_num;
    static int           color_num;
    static int           plane_num;
    static int           result;
    static unsigned char tint;

    /* Allocate memory to save screen when it's switched. */
    result=TRUE;
    for (plane_num=0; ((result) && (plane_num < 4)); plane_num++)
      result=((video_plane[plane_num]
       =(long huge *) halloc(NUM_CELLS,sizeof(char))) != NULL);

    if (result)
      {
        VioScrLock((USHORT) LOCKIO_WAIT,(PBYTE) &scr_lock,(HVIO) 0);
    
        /* Save current video mode. */
        default_video_mode.cb=sizeof(VIOMODEINFO);
        VioGetMode((PVIOMODEINFO) &default_video_mode,(HVIO) 0);
    
        /* Switch to 640 x 480 x 16 VGA mode. */
        memcpy((void *) &maze_video_mode,(const void *) &default_video_mode,
         sizeof(VIOMODEINFO));
        maze_video_mode.fbType=VGMT_GRAPHICS|VGMT_OTHER;
        maze_video_mode.color=COLORS_16;
        maze_video_mode.col=80;
         maze_video_mode.row=25;
        maze_video_mode.hres=NUM_X_PIXELS;
        maze_video_mode.vres=NUM_Y_PIXELS;
        if (result=(VioSetMode((PVIOMODEINFO) &maze_video_mode,(HVIO) 0)
         == (USHORT) 0))
          {
            /* Set up palette for invisible screen redraw. */
            invisible_palette=(PVIOPALSTATE) &invisible_palette_byte[0];
            invisible_palette->cb=(USHORT) sizeof(invisible_palette_byte);
            invisible_palette->type=(USHORT) 0;
            invisible_palette->iFirst=(USHORT) 0;
            for (color_num=0; color_num < NUM_COLORS; color_num++)
              invisible_palette->acolor[color_num]=(USHORT) 0;
    
            /* Set up shades of gray, etc. for drawing maze. */
            maze_palette=(PVIOPALSTATE) &maze_palette_byte[0];
            maze_palette->cb=(USHORT) sizeof(maze_palette_byte);
            maze_palette->type=(USHORT) 0;
            maze_palette->iFirst=(USHORT) 0;
            for (color_num=0; color_num < NUM_COLORS; color_num++)
              maze_palette->acolor[color_num]=(USHORT) color_num;
            VioSetState(maze_palette,(HVIO) 0);
            maze_color.cb=(USHORT) sizeof(maze_color);
            maze_color.type=(USHORT) 3;
            maze_color.firstcolorreg=(USHORT) 0;
            maze_color.numcolorregs=(USHORT) NUM_COLORS;
            maze_color.colorregaddr=(PCH) &maze_rgb[0];
            tint=(unsigned char) 0;
            for (color_num=0; color_num < (NUM_COLORS-1); color_num++)
              {
                maze_rgb[color_num].red=tint;
                maze_rgb[color_num].green=tint;
                maze_rgb[color_num].blue=tint;
                tint+=((unsigned char) RGB_INCREMENT);
              }
            maze_rgb[color_num].red=tint;
            maze_rgb[color_num].green=(unsigned char) 0;
            maze_rgb[color_num].blue=(unsigned char) 0;
            VioSetState(&maze_color,(HVIO) 0);
    
            /* Locate physical video buffer. */
            FP_SEG(phys_buf.pBuf)=0x000a;
            FP_OFF(phys_buf.pBuf)=0;
            phys_buf.cb=NUM_CELLS;
            VioGetPhysBuf((PVIOPHYSBUF) &phys_buf,(USHORT) 0);
            VGA_base_adr=phys_buf.asel[0];
    
            /* Clear screen. */
            FP_SEG(buffer)=phys_buf.asel[0];
            for (cell_num=(USHORT) 0; cell_num < (USHORT) NUM_CELLS; cell_num++)
              {
                FP_OFF(buffer)=cell_num;
                *buffer='\0';
              }
    
            /* Start thread to save/redraw screen when screen is switched. */
            DosCreateThread((PFNTHREAD) save_redraw_thread,
             (PTID) &save_redraw_id,(PBYTE) 
             (save_redraw_thread_stack+sizeof(save_redraw_thread_stack)));
    
            /* Start thread to keep screen in 640 x 480 x 16 VGA mode. */
            DosCreateThread((PFNTHREAD) mode_thread,
             (PTID) &mode_thread_stack,
             (PBYTE) (mode_thread_stack+sizeof(mode_thread_stack)));
          }
        VioScrUnLock((HVIO) 0);
      }
    return(result);
  }

static void set_initial_video_mode()
  {
    VioScrLock((USHORT) LOCKIO_WAIT,(PBYTE) &scr_lock,(HVIO) 0);
    VioSetMode((PVIOMODEINFO) &default_video_mode,(HVIO) 0);
    VioScrUnLock((HVIO) 0);
    hfree((void huge *) (video_plane[3]));
    hfree((void huge *) (video_plane[2]));
    hfree((void huge *) (video_plane[1]));
    hfree((void huge *) (video_plane[0]));
    return;
  }

static void set_pixel(x,y,color)
  int   x;
  int   y;
  short color;
    {
      int   bit_mask;
      char  *cell;
      int   dummy;
    
      VioScrLock((USHORT) LOCKIO_WAIT,(PBYTE) &scr_lock,(HVIO) 0);
      FP_SEG(cell)=VGA_base_adr;
      FP_OFF(cell)=y*80+x/8;
      bit_mask=0x80>>(x % 8);
      outp(VGA_control,VGA_bit_mask);
      outp(VGA_control_data,bit_mask);
      outp(VGA_control,VGA_mode);
      outp(VGA_control_data,2);
      dummy=*cell; 
      *cell=(char) color;
      outp(VGA_control,VGA_mode);
      outp(VGA_control_data,0);
      outp(VGA_control,VGA_bit_mask);
      outp(VGA_control_data,0xff);
      VioScrUnLock((HVIO) 0);
      return;
    }

static void save_redraw_thread()
  {
    long         *buffer;
    unsigned     count;
    long         dummy;
    VIOMODEINFO  mode_info; 
    int          plane_num;
    int          power_of_2;
    int          save_redraw_cmd;

    while (TRUE)
      {
        VioSavRedrawWait(VSRWI_SAVEANDREDRAW,&save_redraw_cmd,0);
        if (save_redraw_cmd == VSRWN_SAVE)
          {
            /* Save a copy of the screen mode. */
            mode_info.cb=sizeof(VIOMODEINFO);
            VioGetMode((PVIOMODEINFO) &mode_info,(HVIO) 0);

            /* Save the contents of the screen. */
            FP_SEG(buffer)=VGA_base_adr;
            for (plane_num=0; plane_num < 4; plane_num++)
              {
                outp(VGA_control,VGA_read_map);
                outp(VGA_control_data,plane_num);
                for (count=0; count < NUM_CELLS; count+=4)
                  {
                    FP_OFF(buffer)=count;
                    (video_plane[plane_num])[count>>2]=*buffer;
                  }
              }

            outp(VGA_sequence,VGA_map_mask); 
            outp(VGA_sequence_data,0xff);
          }
        else
          {
            /* Restore the screen mode. */
            VioSetMode((PVIOMODEINFO) &mode_info,(HVIO) 0);

            /* Set the screen up for invisible restore. */
            VioSetState((PVOID) invisible_palette,(HVIO) 0);

            /* Reset the colors. */
            VioSetState((PVOID) &maze_color,(HVIO) 0);

            /* Restore the screen. */
            FP_SEG(buffer)=VGA_base_adr;
            power_of_2=1;
            for (plane_num=0; plane_num < 4; plane_num++)
              {
                outp(VGA_sequence,VGA_map_mask);
                outp(VGA_sequence_data,power_of_2);
                for (count=0; count < NUM_CELLS; count+=4)
                  {
                    FP_OFF(buffer)=count;
                    dummy=*buffer;
                    *buffer=(video_plane[plane_num])[count>>2];
                  }
                power_of_2*=2;
              }

            outp(VGA_sequence,VGA_map_mask);
            outp(VGA_sequence_data,0xff);

            /* Make the screen visible. */
            VioSetState((PVOID) maze_palette,(HVIO) 0);
          }
      }
    return;
  }

static void mode_thread()
  {
    USHORT mode_cmd;

    while (TRUE)
      {
        VioModeWait((USHORT) 0,(PUSHORT) &mode_cmd,(HVIO) 0);
        VioSetMode((PVIOMODEINFO) &maze_video_mode,(HVIO) 0);
      }
    return;
  }
