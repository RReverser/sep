/*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
*
* This file is part of SEP
*
* Copyright 1993-2011 Emmanuel Bertin -- IAP/CNRS/UPMC
* Copyright 2014 SEP developers
*
* SEP is free software: you can redistribute it and/or modify
* it under the terms of the GNU Lesser General Public License as published by
* the Free Software Foundation, either version 3 of the License, or
* (at your option) any later version.
*
* SEP is distributed in the hope that it will be useful,
* but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
* GNU Lesser General Public License for more details.
*
* You should have received a copy of the GNU Lesser General Public License
* along with SEP.  If not, see <http://www.gnu.org/licenses/>.
*
*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*/

/* Note: was extract.c in SExtractor. */

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "sep.h"
#include "sepcore.h"
#include "extract.h"

#define	NOBJ 256  /* starting number of obj. */

void lutzsort(infostruct *, objliststruct *);

static const infostruct initinfo = {
	.firstpix = -1,
	.lastpix = -1
};

/******************************* lutzalloc ***********************************/
/*
Allocate once for all memory space for buffers used by lutz().
*/
int lutzalloc(int width, int height, lutz_buffers *lutz_buf)
{
  int *discant;
  int stacksize, i, status=RETURN_OK;

  stacksize = width+1;
  lutz_buf->xmin = lutz_buf->ymin = 0;
  lutz_buf->xmax = width-1;
  lutz_buf->ymax = height-1;
  QMALLOC(lutz_buf->info, infostruct, stacksize, status);
  QMALLOC(lutz_buf->store, infostruct, stacksize, status);
  QMALLOC(lutz_buf->marker, char, stacksize, status);
  QMALLOC(lutz_buf->psstack, pixstatus, stacksize, status);
  QMALLOC(lutz_buf->start, int, stacksize, status);
  QMALLOC(lutz_buf->end, int, stacksize, status);
  QMALLOC(lutz_buf->discan, int, stacksize, status);
  discant = lutz_buf->discan;
  lutz_buf->curpixinfo = initinfo;
  for (i=stacksize; i--;)
    *(discant++) = -1;

  return status;

 exit:
  lutzfree(lutz_buf);

  return status;
}

/******************************* lutzfree ************************************/
/*
Free once for all memory space for buffers used by lutz().
*/
void lutzfree(lutz_buffers *lutz_buf)
{
  free(lutz_buf->discan);
  lutz_buf->discan = NULL;
  free(lutz_buf->info);
  lutz_buf->info = NULL;
  free(lutz_buf->store);
  lutz_buf->store = NULL;
  free(lutz_buf->marker);
  lutz_buf->marker = NULL;
  free(lutz_buf->psstack);
  lutz_buf->psstack = NULL;
  free(lutz_buf->start);
  lutz_buf->start = NULL;
  free(lutz_buf->end);
  lutz_buf->end = NULL;
}

/********************************** lutz *************************************/
/*
C implementation of R.K LUTZ' algorithm for the extraction of 8-connected pi-
xels in an image
*/
int lutz(pliststruct *plistin,
	 int *objrootsubmap, int subx, int suby, int subw,
	 objstruct *objparent, objliststruct *objlist, int minarea,
	 lutz_buffers *lutz_buf)
{
  objstruct		*obj;
  pliststruct		*plist,*pixel, *plistint;

  char			newmarker;
  int			cn, co, luflag, pstop, xl,xl2,yl,
                        out, deb_maxarea, stx,sty,enx,eny, step,
                        nobjm = NOBJ,
			inewsymbol, *iscan;
  short		        trunflag;
  PIXTYPE		thresh;
  pixstatus		cs, ps;

  out = RETURN_OK;

  deb_maxarea = minarea<MAXDEBAREA?minarea:MAXDEBAREA; /* 3 or less */
  plistint = plistin;
  stx = objparent->xmin;
  sty = objparent->ymin;
  enx = objparent->xmax;
  eny = objparent->ymax;
  thresh = objlist->thresh;
  cn = 0;

  iscan = objrootsubmap + (sty-suby)*subw + (stx-subx);

  /* As we only analyse a fraction of the map, a step occurs between lines */
  step = subw - (++enx-stx);
  eny++;

  /*------Allocate memory to store object data */
  free(objlist->obj);

  if (!(obj=objlist->obj=(objstruct *)malloc(nobjm*sizeof(objstruct))))
    {
      out = MEMORY_ALLOC_ERROR;
      plist = NULL;			/* To avoid gcc -Wall warnings */
      goto exit_lutz;
    }

  /*------Allocate memory for the pixel list */
  free(objlist->plist);
  if (!(objlist->plist
	= (pliststruct *)malloc((eny-sty)*(enx-stx)*plistsize)))
    {
      out = MEMORY_ALLOC_ERROR;
      plist = NULL;			/* To avoid gcc -Wall warnings */
      goto exit_lutz;
    }

  pixel = plist = objlist->plist;

  /*----------------------------------------*/
  for (xl=stx; xl<=enx; xl++)
    lutz_buf->marker[xl] = 0;

  objlist->nobj = 0;
  co = pstop = 0;
  lutz_buf->curpixinfo.pixnb = 1;

  for (yl=sty; yl<=eny; yl++, iscan += step)
    {
      ps = COMPLETE;
      cs = NONOBJECT;
      trunflag = (yl==0 || yl==lutz_buf->ymax) ? SEP_OBJ_TRUNC : 0;
      if (yl==eny)
	iscan = lutz_buf->discan;

      for (xl=stx; xl<=enx; xl++)
	{
	  newmarker = lutz_buf->marker[xl];
	  lutz_buf->marker[xl] = 0;
	  if ((inewsymbol = (xl!=enx)?*(iscan++):-1) < 0)
	    luflag = 0;
	  else
	    {
	      lutz_buf->curpixinfo.flag = trunflag;
	      plistint = plistin+inewsymbol;
	      luflag = (PLISTPIX(plistint, cdvalue) > thresh?1:0);
	    }
	  if (luflag)
	    {
	      if (xl==0 || xl==lutz_buf->xmax)
		lutz_buf->curpixinfo.flag |= SEP_OBJ_TRUNC;
	      memcpy(pixel, plistint, (size_t)plistsize);
	      PLIST(pixel, nextpix) = -1;
	      lutz_buf->curpixinfo.lastpix = lutz_buf->curpixinfo.firstpix = cn;
	      cn += plistsize;
	      pixel += plistsize;

	      /*----------------- Start Segment -----------------------------*/
	      if (cs != OBJECT)
		{
		  cs = OBJECT;
		  if (ps == OBJECT)
		    {
		      if (lutz_buf->start[co] == UNKNOWN)
			{
			  lutz_buf->marker[xl] = 'S';
			  lutz_buf->start[co] = xl;
			}
		      else  lutz_buf->marker[xl] = 's';
		    }
		  else
		    {
		      lutz_buf->psstack[pstop++] = ps;
		      lutz_buf->marker[xl] = 'S';
		      lutz_buf->start[++co] = xl;
		      ps = COMPLETE;
		      lutz_buf->info[co] = initinfo;
		    }
		}
	    }

	  /*-------------------Process New Marker ---------------------------*/
	  if (newmarker)
	    {
	      if (newmarker == 'S')
		{
		  lutz_buf->psstack[pstop++] = ps;
		  if (cs == NONOBJECT)
		    {
		      lutz_buf->psstack[pstop++] = COMPLETE;
		      lutz_buf->info[++co] = lutz_buf->store[xl];
		      lutz_buf->start[co] = UNKNOWN;
		    }
		  else
		    update(&lutz_buf->info[co], &lutz_buf->store[xl], plist);
		  ps = OBJECT;
		}

	      else if (newmarker == 's')
		{
		  if ((cs == OBJECT) && (ps == COMPLETE))
		    {
		      pstop--;
		      xl2 = lutz_buf->start[co];
		      update(&lutz_buf->info[co-1], &lutz_buf->info[co], plist);
		      if (lutz_buf->start[--co] == UNKNOWN)
			lutz_buf->start[co] = xl2;
		      else
			lutz_buf->marker[xl2] = 's';
		    }
		  ps = OBJECT;
		}
	      else if (newmarker == 'f')
		ps = INCOMPLETE;
	      else if (newmarker == 'F')
		{
		  ps = lutz_buf->psstack[--pstop];
		  if ((cs == NONOBJECT) && (ps == COMPLETE))
		    {
		      if (lutz_buf->start[co] == UNKNOWN)
			{
			  if ((int)lutz_buf->info[co].pixnb >= deb_maxarea)
			    {
			      if (objlist->nobj>=nobjm)
				if (!(obj = objlist->obj = (objstruct *)
				      realloc(obj, (nobjm+=nobjm/2)*
					      sizeof(objstruct))))
				  {
				    out = MEMORY_ALLOC_ERROR;
				    goto exit_lutz;
				  }
			      lutzsort(&lutz_buf->info[co], objlist);
			    }
			}
		      else
			{
			  lutz_buf->marker[lutz_buf->end[co]] = 'F';
			  lutz_buf->store[lutz_buf->start[co]] = lutz_buf->info[co];
			}
		      co--;
		      ps = lutz_buf->psstack[--pstop];
		    }
		}
	    }
	  /* end process new marker -----------------------------------------*/

	  if (luflag)
	    update (&lutz_buf->info[co],&lutz_buf->curpixinfo, plist);
	  else
	    {
	      /* ----------------- End Segment ------------------------------*/
	      if (cs == OBJECT)
		{
		  cs = NONOBJECT;
		  if (ps != COMPLETE)
		    {
		      lutz_buf->marker[xl] = 'f';
		      lutz_buf->end[co] = xl;
		    }
		  else
		    {
		      ps = lutz_buf->psstack[--pstop];
		      lutz_buf->marker[xl] = 'F';
		      lutz_buf->store[lutz_buf->start[co]] = lutz_buf->info[co];
		      co--;
		    }
		}
	    }
	}
    }

 exit_lutz:

  if (objlist->nobj && out == RETURN_OK)
    {
      if (!(objlist->obj=
	    (objstruct *)realloc(obj, objlist->nobj*sizeof(objstruct))))
	out = MEMORY_ALLOC_ERROR;
    }
  else
    {
      free(obj);
      objlist->obj = NULL;
    }

  if (cn && out == RETURN_OK)
    {
      if (!(objlist->plist=(pliststruct *)realloc(plist,cn)))
	out = MEMORY_ALLOC_ERROR;
    }
  else
    {
      free(objlist->plist);
      objlist->plist = NULL;
    }

  return out;
}

/********************************* lutzsort ***********************************/
/*
Add an object to the object list based on info (pixel info)
*/
void  lutzsort(infostruct *info, objliststruct *objlist)
{
  objstruct *obj = objlist->obj+objlist->nobj;

  memset(obj, 0, (size_t)sizeof(objstruct));
  obj->firstpix = info->firstpix;
  obj->lastpix = info->lastpix;
  obj->flag = info->flag;
  objlist->npix += info->pixnb;

  preanalyse(objlist->nobj, objlist);

  objlist->nobj++;

  return;
}

/********************************* update ************************************/
/*
update object's properties each time one of its pixels is scanned by lutz()
*/
void  update(infostruct *infoptr1, infostruct *infoptr2, pliststruct *pixel)
{
  infoptr1->pixnb += infoptr2->pixnb;
  infoptr1->flag |= infoptr2->flag;
  if (infoptr1->firstpix == -1)
    {
      infoptr1->firstpix = infoptr2->firstpix;
      infoptr1->lastpix = infoptr2->lastpix;
    }
  else if (infoptr2->lastpix != -1)
    {
      PLIST(pixel+infoptr1->lastpix, nextpix) = infoptr2->firstpix;
      infoptr1->lastpix = infoptr2->lastpix;
    }

  return;
}
