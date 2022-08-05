"""
olcPixelGameEngine written in Python.

Original Implementation by Javidx9: https://github.com/OneLoneCoder/olcPixelGameEngine

@author Ben Antonellis

"""

from enum import Enum, auto
from functools import singledispatchmethod
from re import A
from tkinter import N
from typing import List, TypeVar, Generic, Dict, Callable, Union
from math import floor, ceil, sqrt, cos, sin, atan2
from os.path import exists, getsize
from dataclasses import dataclass
import struct
import sys
from threading import Thread
import time

from OpenGL.GL import *
from OpenGL.GLU import *
from OpenGL.GLUT import *

T = TypeVar('T')

class PixelGameEngine: pass
class Sprite: pass

MOUSE_BUTTONS: int = 5
DEFAULT_ALPHA: int = 0xFF
DEFAULT_PIXEL: int = DEFAULT_ALPHA << 25
TAB_SIZE: int = 4

@dataclass
class HWButton():
    pressed: bool=False,
    released: bool=False,
    held: bool=False

class ReturnCode(Enum):
    FAIL = 0,
    OK = 1,
    NO_FILE = -1
    
class PixelMode(Enum):
    NORMAL = auto(),
    MASK = auto(),
    ALPHA = auto(),
    CUSTOM = auto()

class v2d_generic(Generic[T]):
    
    def __init__(self, x: T=0, y: T=0):
        self.x = x
        self.y = y

    def mag(self) -> T:
        return T(sqrt(self.x * self.x + self.y * self.y))

    def mag2(self) -> T:
        return self.x * self.x + self.y * self.y

    def norm(self) -> 'v2d_generic':
        return v2d_generic(self.x * (1 / self.mag()), self.y * (1 / self.mag()))

    def perp(self) -> 'v2d_generic':
        return v2d_generic(-self.y, self.x)

    def floor(self) -> 'v2d_generic':
        return v2d_generic(floor(self.x), floor(self.y))

    def ceil(self) -> 'v2d_generic':
        return v2d_generic(ceil(self.x), ceil(self.y))

    def max(self, v: 'v2d_generic') -> 'v2d_generic':
        return v2d_generic(max(self.x, v.x), max(self.y, v.y))
    
    def min(self, v: 'v2d_generic') -> 'v2d_generic':
        return v2d_generic(min(self.x, v.x), min(self.y, v.y))

    def cart(self) -> 'v2d_generic':
        return v2d_generic(cos(self.y) * self.x, sin(self.y) * self.x)

    def polar(self) -> 'v2d_generic':
        return v2d_generic(self.mag(), atan2(self.y, self.x))

    def dot(self, rhs: 'v2d_generic') -> T:
        return self.x * rhs.x + self.y * rhs.y
    
    def cross(self, rhs: 'v2d_generic') -> T:
        return self.x * rhs.y - self.y * rhs.x

    def __add__(self, rhs: 'v2d_generic') -> 'v2d_generic':
        return v2d_generic(self.x + rhs.x, self.y + rhs.y)
    
    def __sub__(self, rhs: 'v2d_generic') -> 'v2d_generic':
        return v2d_generic(self.x - rhs.x, self.y - rhs.y)
    
    def __mul__(self, rhs: T) -> 'v2d_generic':
        return v2d_generic(self.x * rhs.x, self.y * rhs.y)
    
    def __div__(self, rhs: T) -> 'v2d_generic':
        return v2d_generic(self.x / rhs.x, self.y / rhs.y)

    def __Truediv__(self, rhs: T) -> 'v2d_generic':
        return self.__div__(rhs)

    def __iadd__(self, rhs: 'v2d_generic') -> 'v2d_generic':
        self.x += rhs.x
        self.y += rhs.y
        return self
    
    def __isub__(self, rhs: 'v2d_generic') -> 'v2d_generic':
        self.x -= rhs.x
        self.y -= rhs.y
        return self
    
    def __imul__(self, rhs: T) -> 'v2d_generic':
        self.x *= rhs
        self.y *= rhs
        return self

    def __idiv__(self, rhs: T) -> 'v2d_generic':
        self.x /= rhs
        self.y /= rhs
        return self

    def __iTruediv__(self, rhs: T) -> 'v2d_generic':
        self.x /= rhs
        self.y /= rhs
        return self
    
    def __eq__(self, rhs: 'v2d_generic') -> bool:
        return self.x == rhs.x and self.y == rhs.y
    
    def __ne__(self, rhs: 'v2d_generic') -> bool:
        return self.x != rhs.x or self.y != rhs.y
    
    def __str__(self) -> str:
        return f'({self.x}, {self.y})'
    
    def __int__(self) -> int:
        return v2d_generic(int(self.x), int(self.y))
    
    def __float__(self) -> float:
        return v2d_generic(float(self.x), float(self.y))

    def __lt__(self, rhs: 'v2d_generic') -> bool:
        return self.y < rhs.y or (self.y == rhs.y and self.x < rhs.x)
    
    def __gt__(self, rhs: 'v2d_generic') -> bool:
        return self.y > rhs.y or (self.y == rhs.y and self.x > rhs.x)

vi2d = v2d_generic[int]
vf2d = v2d_generic[float]

class ResourceBuffer:
    def __init__(self, data: bytes, offset: int, size: int):
        self.memory = []
        self.memory.extend(data[offset:offset + size])

class ResourcePack:

    @dataclass
    class ResourceFile:
        size: int
        offset: int

    def __init__(self):
        self.map_files = {} # {str: ResourceFile}
        self.base_file = None # FileStream

    def AddFile(self, file: str) -> bool:
        filename = self.makeposix(file)
        if exists(filename):
            self.map_files[filename] = self.ResourceFile(size=getsize(filename), offset=0)
            return True
        return False

    def LoadPack(self, file: str, key: str) -> bool:
        self.base_file = open(file, 'rb')
        if not self.base_file: return False

        index_size = int(self.base_file.read(4)) # uint32_t is four bytes
        buffer = [self.base_file.read(1) for _ in range(index_size)]
        decoded = self.scramble(buffer, key)
        pos = 0
        map_entries = int(self.base_file.read(4)) # uint32_t is four bytes
        for _ in range(map_entries):
            name_size = int(self.base_file.read(4))
            name = self.base_file.read(name_size).decode('utf-8')
            self.map_files[name] = self.ResourceFile(
                size=int(self.base_file.read(4)),
                offset=int(self.base_file.read(4))
            )
        return True
    
    def SavePack(self, file: str, key: str) -> bool:
        writer = open(file, 'wb')
        if not writer: return False

        index_size = 0
        writer.write(struct.pack('<I', index_size))
        map_size = len(self.map_files)
        writer.write(struct.pack('<I', map_size))

        for name in self.map_files:
            writer.write(len(name).to_bytes(4, 'little'))
            writer.write(name.encode('utf-8'))
            writer.write(struct.pack('<I', self.map_files[name].size))
            writer.write(struct.pack('<I', self.map_files[name].offset))
        
        offset = writer.tell()
        index_size = int(offset)
        for name in self.map_files:
            self.map_files[name].offset = offset
            f = open(name, 'rb')
            buffer = f.read(self.map_files[name].size)
            f.close()
            writer.write(buffer)
            offset += self.map_files[name].size

        stream = []
        stream.append(map_size)
        for name in self.map_files:
            stream.append(len(name))
            stream.append(name)
            stream.append(self.map_files[name].size)
            stream.append(self.map_files[name].offset)

        index_string = self.scramble(stream, key)
        index_string_len = len(index_string)
        writer.seek(0)
        writer.write(struct.pack('<I', index_string_len))
        writer.write(index_string)
        writer.close()
        return True

    def GetFileBuffer(self, file: str) -> ResourceBuffer:
        return ResourceBuffer(self.base_file, self.map_files[file].offset, self.map_files[file].size)

    def Loaded(self) -> bool:
        return self.base_file is not None

    def scramble(self, data: List[str], key: str) -> List[str]:
        if key == '': return data
        output = []
        c = 0
        for _, value in enumerate(data):
            output.append(value ^ key[c % len(key)])
            c += 1
        return output

    def makeposix(self, path: str) -> str:
        return path.replace('\\', '/')

class ImageLoader:

    def __init__(self):
        pass
    
    def LoadImageResource(self, sprite: 'Sprite', file: str, pack: 'ResourcePack') -> 'ReturnCode':
        return ReturnCode.OK
    
    def SaveImageResource(self, sprite: 'Sprite', file: str) -> 'ReturnCode':
        return ReturnCode.OK

class Pixel:

    def __init__(self, red: int, green: int, blue: int, alpha: int = DEFAULT_ALPHA):
        self.r = red
        self.g = green
        self.b = blue
        self.a = alpha
        self.n = self.r | (self.g << 8) | (self.b << 16) | (self.a << 24)

    def __eq__(self, other: 'Pixel') -> bool:
        return self.n == other.n

    def __ne__(self, other: 'Pixel') -> bool:
        return self.n != other.n

    def __mul__(self, i: float) -> 'Pixel':
        return Pixel(
            int(min(255.0, max(0.0, float(self.r) * i))),
            int(min(255.0, max(0.0, float(self.g) * i))),
            int(min(255.0, max(0.0, float(self.b) * i))),
            self.a
        )

    def __div__(self, i: float) -> 'Pixel':
        return Pixel(
            int(min(255.0, max(0.0, float(self.r) / i))),
            int(min(255.0, max(0.0, float(self.g) / i))),
            int(min(255.0, max(0.0, float(self.b) / i))),
            self.a
        )

    def __imul__(self, i: float) -> 'Pixel':
        self.r = int(min(255.0, max(0.0, float(self.r) * i)))
        self.g = int(min(255.0, max(0.0, float(self.g) * i)))
        self.b = int(min(255.0, max(0.0, float(self.b) * i)))
        return self

    def __idiv__(self, i: float) -> 'Pixel':
        self.r = int(min(255.0, max(0.0, float(self.r) / i)))
        self.g = int(min(255.0, max(0.0, float(self.g) / i)))
        self.b = int(min(255.0, max(0.0, float(self.b) / i)))
        return self

    def __add__(self, p: object) -> 'Pixel':
        return Pixel(
            int(min(255, max(0, int(self.r) + int(p.r)))),
            int(min(255, max(0, int(self.g) + int(p.g)))),
            int(min(255, max(0, int(self.b) + int(p.b)))),
            self.a
        )

    def __sub__(self, p: object) -> 'Pixel':
        return Pixel(
            int(min(255, max(0, int(self.r) - int(p.r)))),
            int(min(255, max(0, int(self.g) - int(p.g)))),
            int(min(255, max(0, int(self.b) - int(p.b)))),
            self.a
        )

    def __iadd__(self, p: object) -> 'Pixel':
        self.r = int(min(255, max(0, int(self.r) + int(p.r))))
        self.g = int(min(255, max(0, int(self.g) + int(p.g))))
        self.b = int(min(255, max(0, int(self.b) + int(p.b))))
        return self

    def __isub__(self, p: object) -> 'Pixel':
        self.r = int(min(255, max(0, int(self.r) - int(p.r))))
        self.g = int(min(255, max(0, int(self.g) - int(p.g))))
        self.b = int(min(255, max(0, int(self.b) - int(p.b))))
        return self

    def inv(self) -> 'Pixel':
        return Pixel(
            int(min(255, max(0, 255 - int(self.r)))),
            int(min(255, max(0, 255 - int(self.g)))),
            int(min(255, max(0, 255 - int(self.b)))),
            self.a
        )

def PixelF(red: float, green: float, blue: float, alpha: float) -> 'Pixel':
    return Pixel(
        int(red * 255.0),
        int(green * 255.0),
        int(blue * 255.0),
        int(alpha * 255.0)
    )

def PixelLerp(p1: 'Pixel', p2: 'Pixel', t: float) -> 'Pixel':
    return (p2 * t) + p1 * (1.0 - t)

GREY = Pixel(192, 192, 192) ; DARK_GREY = Pixel(128, 128, 128) ; VERY_DARK_GREY = Pixel(64, 64, 64)
RED = Pixel(255, 0, 0) ; DARK_RED = Pixel(128, 0, 0) ; VERY_DARK_RED = Pixel(64, 0, 0)
YELLOW = Pixel(255, 255, 0) ; DARK_YELLOW = Pixel(128, 128, 0) ; VERY_DARK_YELLOW = Pixel(64, 64, 0)
GREEN = Pixel(0, 255, 0) ; DARK_GREEN = Pixel(0, 128, 0) ; VERY_DARK_GREEN = Pixel(0, 64, 0)
CYAN = Pixel(0, 255, 255) ; DARK_CYAN = Pixel(0, 128, 128) ; VERY_DARK_CYAN = Pixel(0, 64, 64)
BLUE = Pixel(0, 0, 255) ; DARK_BLUE = Pixel(0, 0, 128) ; VERY_DARK_BLUE = Pixel(0, 0, 64)
MAGENTA = Pixel(255, 0, 255) ; DARK_MAGENTA = Pixel(128, 0, 128) ; VERY_DARK_MAGENTA = Pixel(64, 0, 64)
WHITE = Pixel(255, 255, 255) ; BLACK = Pixel(0, 0, 0) ; BLANK = Pixel(0, 0, 0, 0)

Key = Enum("Key", "A B C D E F G H I J K L M N O P Q R S T U V W X Y Z K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 UP DOWN LEFT RIGHT SPACE TAB SHIFT CTRL INS DEL HOME END PGUP PGDN BACK ESCAPE RETURN ENTER PAUSE SCROLL NP0 NP1 NP2 NP3 NP4 NP5 NP6 NP7 NP8 NP9 NP_MUL NP_DIV NP_ADD NP_SUB NP_DECIMAL PERIOD EQUALS COMMA MINUS OEM_1 OEM_2 OEM_3 OEM_4 OEM_5 OEM_6 OEM_7 OEM_8 CAPS_LOCK ENUM_END NONE")
Mouse = Enum("Mouse", "LEFT RIGHT MIDDLE")

class Sprite:

    class SpriteMode(Enum):
        NORMAL = auto(),
        PERIODIC = auto(),
        CLAMP = auto()

    class SpriteFlip(Enum):
        NONE = auto(),
        HORIZ = auto(),
        VERT = auto()

    def __init__(self, **kwargs):
        self.col_data: List['Pixel'] = [] # List of pixels
        self.mode_sample = self.SpriteMode.NORMAL
        if 'w' in kwargs and 'h' in kwargs:
            self.w = kwargs['w']
            self.h = kwargs['h']
            self.col_data.extend([0] * (self.w * self.h))
        elif 'image' in kwargs and 'pack' in kwargs:
            self.LoadFromFile(kwargs['image'], kwargs['pack'])
        elif kwargs == {}:
            self.w = 0
            self.h = 0

    def SetSampleMode(self, mode: int) -> None:
        self.mode_sample = mode

    @singledispatchmethod
    def GetPixel(self, arg):
        raise NotImplementedError(f"Sprite.GetPixel: Invalid Arugment: {arg}")

    @GetPixel.register
    def _(self, vec: 'v2d_generic') -> 'Pixel':
        return self.GetPixel(vec.x, vec.y)
    
    @GetPixel.register
    def _(self, x: int, y: int) -> 'Pixel':
        if self.mode_sample == self.SpriteMode.NORMAL:
            if x > 0 and x < self.w and y >= 0 and y < self.h:
                return self.col_data[y * self.w + x]
            return Pixel(0, 0, 0, 0)
        if self.mode_sample == self.SpriteMode.PERIODIC:
            return self.col_data[abs(y % self.h) * self.w + abs(x % self.w)]
        return self.col_data[max(0, min(y, self.h - 1)) * self.w + max(0, min(x, self.w - 1))]

    @singledispatchmethod
    def SetPixel(self, arg):
        raise NotImplementedError(f"Sprite.SetPixel: Invalid Arugment: {arg}")

    @SetPixel.register
    def _(self, vec: 'v2d_generic', p: 'Pixel') -> bool:
        return self.SetPixel(vec.x, vec.y, p)

    @SetPixel.register
    def _(self, x: int, y: int, p: 'Pixel') -> bool:
        if x > 0 and x < self.w and y >= 0 and y < self.h:
            self.col_data[y * self.w + x] = p
            return True
        return False

    def Sample(self, x: float, y: float) -> 'Pixel':
        return Pixel(
            min(int(x * float(self.w)), self.w - 1),
            min(int(y * float(self.h)), self.h - 1),
        )

    def SampleBL(self, u: float, v: float) -> 'Pixel':
        u = u * self.w - 0.5
        v = v * self.h - 0.5
        x = int(floor(u))
        y = int(floor(v))
        u_ratio = float(u - x)
        v_ratio = float(v - y)
        u_opposite = 1 - u_ratio
        v_opposite = 1 - v_ratio

        p1 = self.GetPixel(max(x, 0), max(y, 0))
        p2 = self.GetPixel(min(x + 1, int(self.w - 1)), max(y, 0))
        p3 = self.GetPixel(max(x, 0), min(y + 1, int(self.h - 1)))
        p4 = self.GetPixel(min(x + 1, int(self.w - 1)), min(y + 1, int(self.h - 1)))

        return Pixel(
            int(p1.r * u_opposite + p2.r * u_ratio) * v_opposite + (p3.r * u_opposite + p4.r * u_ratio) * v_ratio,
            int(p1.g * u_opposite + p2.g * u_ratio) * v_opposite + (p3.g * u_opposite + p4.g * u_ratio) * v_ratio,
            int(p1.b * u_opposite + p2.b * u_ratio) * v_opposite + (p3.b * u_opposite + p4.b * u_ratio) * v_ratio,
        )

    def GetData(self) -> List['Pixel']:
        return self.col_data
    
    def LoadFromFile(self, image: str, pack: object) -> 'ReturnCode':
        raise NotImplementedError("Sprite.LoadFromFile: Not Implemented")
        #loader.LoadImageResource(image, pack)

    @singledispatchmethod
    def Duplicate(self, arg):
        raise NotImplementedError(f"Sprite.Duplicate: Invalid Arugment: {arg}")
    
    @Duplicate.register
    def _(self) -> 'Sprite':
        sprite = Sprite(w=self.w, h=self.h)
        sprite.mode_sample = self.mode_sample
        sprite.col_data = self.col_data
        return sprite

    @Duplicate.register
    def _(self, pos: 'v2d_generic', size: 'v2d_generic') -> 'Sprite':
        sprite = Sprite(w=size.x, h=size.y)
        for y in range(size.y):
            for x in range(size.x):
                sprite.SetPixel(x, y, self.GetPixel(pos.x + x, pos.y + y))
        return sprite

class Decal:

    class DecalMode(Enum):
        NORMAL = auto(),
        ADDITIVE = auto(),
        MULTIPLICATIVE = auto(),
        STENCIL = auto(),
        ILLUMINATE = auto(),
        WIREFRAME = auto(),
        MODEL3D = auto()

    class DecalStructure(Enum):
        LINE = auto(),
        FAN = auto(),
        STRIP = auto(),
        LIST = auto()

    def __init__(self, sprite: 'Sprite', filter: bool=False, clamp: bool=True):
        self.id = -1
        self.sprite = sprite
        self.uv_scale = vf2d(1, 1)
        self.id = renderer.CreateTexture(sprite.w, sprite.h, filter, clamp)
        self.Update()

    def Update(self) -> None:
        if self.sprite == None: return
        self.uv_scale = vf2d(1.0 / float(self.sprite.w), 1.0 / float(self.sprite.h))
        renderer.ApplyTexture(self.id)
        renderer.UpdateTexture(self.id, self.sprite)

    def UpdateSprite(self) -> None:
        if self.sprite == None: return
        renderer.ApplyTexture(self.id)
        renderer.ReadTexture(self.id, self.sprite)

class Renderable:

    def __init__(self, sprite: 'Sprite', decal: 'Decal'):
        self.sprite = sprite
        self.decal = decal

    def Create(self, width: int, height: int, filter: bool=False, clamp: bool=True) -> None:
        self.sprite = Sprite(w=width, h=height)
        self.decal = Decal(self.sprite, filter, clamp)

    def Load(self, file: str, pack: object, filter: bool=False, clamp: bool=True) -> 'ReturnCode':
        if self.sprite.LoadFromFile(file, pack) == ReturnCode.OK:
            self.decal = Decal(self.sprite, filter, clamp)
            return ReturnCode.OK
        self.sprite = None
        return ReturnCode.NO_FILE

    def Decal(self) -> 'Decal':
        return self.decal
    
    def Sprite(self) -> 'Sprite':
        return self.sprite

@dataclass
class DecalInstance:
    decal: 'Decal'
    pos: 'v2d_generic'
    uv: 'v2d_generic'
    w: List[float]
    tint: List['Pixel']
    mode: 'Decal.DecalMode' = Decal.DecalMode.NORMAL
    structure: 'Decal.DecalStructure' = Decal.DecalStructure.FAN
    points: int = 0

@dataclass
class LayerDesc:
    offset: vf2d = vf2d(0, 0)
    scale: vf2d = vf2d(1, 1)
    show: bool = False
    update: bool = False
    target: 'Renderable' = None
    res_id: int = 0
    decal_instances: List[DecalInstance] = None
    tint: Pixel = WHITE
    func_hook: Callable = None

class Renderer:

    def __init__(self):
        self.fullscreen = False
        self.sync = False
        self.decal_mode = Decal.DecalMode.NORMAL
        self.decal_structure = Decal.DecalStructure.LINE

    def PrepareDevice(self):
        argc = 0
        argv = ""
        glutInit([argc, argv])
        glutInitWindowPosition(0, 0)
        glutInitWindowSize(512, 512)
        glutInitDisplayMode(GLUT_DOUBLE | GLUT_DEPTH | GLUT_RGBA)
        glutCreateWindow("OneLoneCoder.com - Pixel Game Engine")
        glEnable(GL_TEXTURE_2D)
        glHint(GL_PERSPECTIVE_CORRECTION_HINT, GL_NICEST)

    def CreateDevice(self, params: List[str], fullscreen: bool, vsync: bool) -> 'ReturnCode':
        self.fullscreen = fullscreen
        if not vsync:
            glEnable(GL_TEXTURE_2D)
            glHint(GL_PERSPECTIVE_CORRECTION_HINT, GL_NICEST)
        return ReturnCode.OK

    def DestroyDevice(self) -> 'ReturnCode':
        glutDestroyWindow(glutGetWindow())
        return ReturnCode.OK

    def DisplayFrame(self) -> None:
        glutSwapBuffers()

    def PrepareDrawing(self) -> None:
        glEnable(GL_BLEND)
        self.decal_mode = Decal.DecalMode.NORMAL
        self.decal_structure = Decal.DecalStructure.FAN
        glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)

    def SetDecalMode(self, mode: 'Decal.DecalMode') -> None:
        if mode == self.decal_mode: return
        if mode == Decal.DecalMode.NORMAL or mode == Decal.DecalMode.MODEL3D:
            glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)
        elif mode == Decal.DecalMode.ADDITIVE:
            glBlendFunc(GL_SRC_ALPHA, GL_ONE)
        elif mode == Decal.DecalMode.MULTIPLICATIVE:
            glBlendFunc(GL_DST_COLOR, GL_ONE_MINUS_SRC_ALPHA)
        elif mode == Decal.DecalMode.STENCIL:
            glBlendFunc(GL_ZERO, GL_SRC_ALPHA)
        elif mode == Decal.DecalMode.ILLUMINATE:
            glBlendFunc(GL_ONE_MINUS_SRC_ALPHA, GL_SRC_ALPHA)
        elif mode == Decal.DecalMode.WIREFRAME:
            glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)
        self.decal_mode = mode

    def DrawLayerQuad(self, offset: 'v2d_generic', scale: 'v2d_generic', tint: 'Pixel') -> None:
        glBegin(GL_QUADS)
        glColor4ub(tint.r, tint.g, tint.b, tint.a)
        glTexCoord2f(0.0 * scale.x + offset.x, 0.0 * scale.y + offset.y)
        glVertex3f(-1.0, -1.0, 0.0)
        glTexCoord2f(1.0 * scale.x + offset.x, 0.0 * scale.y + offset.y)
        glVertex3f(-1.0, 1.0, 0.0)
        glTexCoord2f(1.0 * scale.x + offset.x, 1.0 * scale.y + offset.y)
        glVertex3f(1.0, -1.0, 0.0)
        glEnd()

    def DrawDecal(self, decal: 'DecalInstance') -> None:
        self.SetDecalMode(decal.DecalMode.NORMAL)
        if decal.sprite is None:
            glBindTexture(GL_TEXTURE_2D, 0)
        else:
            glBindTexture(GL_TEXTURE_2D, decal.id)
        if self.decal_mode != Decal.DecalMode.MODEL3D:
            if self.decal_mode == Decal.DecalMode.WIREFRAME:
                glBegin(GL_LINE_LOOP)
            else:
                if decal.structure == Decal.DecalStructure.FAN:
                    glBegin(GL_TRIANGLE_FAN)
                elif decal.structure == Decal.DecalStructure.STRIP:
                    glBegin(GL_TRIANGLE_STRIP)
                elif decal.structure == Decal.DecalStructure.LIST:
                    glBegin(GL_TRIANGLES)
            for i in range(decal.points):
                glColor4ub(decal.tint[i].r, decal.tint[i].g, decal.tint[i].b, decal.tint[i].a)
                glTexCoord4f(decal.uv[i].x, decal.uv[i].y, 0.0, decal.w[i])
                glVertex2f(decal.pos[i].x, decal.pos[i].y)
            glEnd()

    def CreateTexture(self, width: int, height: int, filter: bool=False, clamp: bool=True) -> int:
        id = 0
        glGenTextures(1, id)
        glBindTexture(GL_TEXTURE_2D, id)
        if filter:
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR)
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR)
        else:
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST)
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST)
        if clamp:
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP)
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP)
        else:
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_REPEAT)
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_REPEAT)
        glTexEnvf(GL_TEXTURE_ENV, GL_TEXTURE_ENV_MODE, GL_MODULATE)
        return id

    def UpdateTexture(self, id: int, sprite: 'Sprite') -> None:
        glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA, sprite.w, sprite.h, 0, GL_RGBA, GL_UNSIGNED_BYTE, sprite.col_data)

    def ReadTexture(self, id: int, sprite: 'Sprite') -> None:
        glReadPixels(0, 0, sprite.w, sprite.h, GL_RGBA, GL_UNSIGNED_BYTE, sprite.col_data)

    def DeleteTexture(self, id: int) -> None:
        glBindTexture(GL_TEXTURE_2D, id)
        
    def ApplyTexture(self, id: int) -> None:
        glBindTexture(GL_TEXTURE_2D, id)

    def ClearBuffer(self, p: 'Pixel', depth: bool) -> None:
        glClearColor(float(p.r) / 255.0, float(p.g) / 255.0, float(p.b) / 255.0, float(p.a) / 255.0)
        glClear(GL_COLOR_BUFFER_BIT)
        if depth:
            glClear(GL_DEPTH_BUFFER_BIT)

    def UpdateViewport(self, pos: 'v2d_generic', size: 'v2d_generic') -> None:
        glViewport(pos.x, pos.y, size.x, size.y)


class Platform:

    def __init__(self):
        self.active_ref = True

    def ApplicationStartUp(self) -> 'ReturnCode': return ReturnCode.OK
    def ApplicationCleanUp(self) -> 'ReturnCode': return ReturnCode.OK
    def ThreadStartUp(self) -> 'ReturnCode': return ReturnCode.OK

    def ThreadCleanUp(self) -> 'ReturnCode':
        renderer.DestroyDevice()
        return ReturnCode.OK

    def CreateGraphics(self, fullscreen: bool, vsync: bool, view_pos: 'v2d_generic', view_size: 'v2d_generic') -> 'ReturnCode':
        if renderer.CreateDevice([], fullscreen, vsync) == ReturnCode.OK:
            renderer.UpdateViewport(view_pos, view_size)
            return ReturnCode.OK
        return ReturnCode.FAIL

    def ExitMainLoop(self) -> None:
        self.ThreadCleanUp()
        self.ApplicationCleanUp()
        sys.exit(0)

    def CreateWindowPane(self, window_pos: 'v2d_generic', window_size: 'v2d_generic', fullscreen: bool) -> 'ReturnCode':
        renderer.PrepareDevice()
        if fullscreen:
            window_size.x = glutGet(GLUT_SCREEN_WIDTH)
            window_size.y = glutGet(GLUT_SCREEN_HEIGHT)
            glutFullScreen()
        else:
            if window_size.x > glutGet(GLUT_SCREEN_WIDTH) or window_size.y > glutGet(GLUT_SCREEN_HEIGHT):
                print("ERROR: The specified window dimensions do not fit on the screen.")
                return ReturnCode.FAIL
            glutReshapeWindow(window_size.x, window_size.y - 1)

        # Create Keyboard Mapping

        map_keys[0x00] = Key.NONE
        map_keys['A'] = Key.A ; map_keys['B'] = Key.B ; map_keys['C'] = Key.C ; map_keys['D'] = Key.D
        map_keys['E'] = Key.E ; map_keys['F'] = Key.F ; map_keys['G'] = Key.G ; map_keys['H'] = Key.H
        map_keys['I'] = Key.I ; map_keys['J'] = Key.J ; map_keys['K'] = Key.K ; map_keys['L'] = Key.L
        map_keys['M'] = Key.M ; map_keys['N'] = Key.N ; map_keys['O'] = Key.O ; map_keys['P'] = Key.P
        map_keys['Q'] = Key.Q ; map_keys['R'] = Key.R ; map_keys['S'] = Key.S ; map_keys['T'] = Key.T
        map_keys['U'] = Key.U ; map_keys['V'] = Key.V ; map_keys['W'] = Key.W ; map_keys['X'] = Key.X
        map_keys['Y'] = Key.Y ; map_keys['Z'] = Key.Z

        map_keys[GLUT_KEY_F1] = Key.F1 ; map_keys[GLUT_KEY_F2] = Key.F2
        map_keys[GLUT_KEY_F3] = Key.F3 ; map_keys[GLUT_KEY_F4] = Key.F4
        map_keys[GLUT_KEY_F5] = Key.F5 ; map_keys[GLUT_KEY_F6] = Key.F6
        map_keys[GLUT_KEY_F7] = Key.F7 ; map_keys[GLUT_KEY_F8] = Key.F8
        map_keys[GLUT_KEY_F9] = Key.F9 ; map_keys[GLUT_KEY_F10] = Key.F10
        map_keys[GLUT_KEY_F11] = Key.F11 ; map_keys[GLUT_KEY_F12] = Key.F12

        map_keys[GLUT_KEY_DOWN] = Key.DOWN ; map_keys[GLUT_KEY_UP] = Key.UP
        map_keys[GLUT_KEY_LEFT] = Key.LEFT ; map_keys[GLUT_KEY_RIGHT] = Key.RIGHT

        map_keys[13] = Key.ENTER ; map_keys[127] = Key.BACK ; map_keys[27] = Key.ESCAPE
        map_keys[9] = Key.TAB ; map_keys[GLUT_KEY_HOME] = Key.HOME
        map_keys[GLUT_KEY_END] = Key.END ; map_keys[GLUT_KEY_PAGE_UP] = Key.PGUP
        map_keys[GLUT_KEY_PAGE_DOWN] = Key.PGDN ; map_keys[GLUT_KEY_INSERT] = Key.INS
        map_keys[32] = Key.SPACE ; map_keys[46] = Key.PERIOD

        map_keys[48] = Key.K0 ; map_keys[49] = Key.K1 ; map_keys[50] = Key.K2 ; map_keys[51] = Key.K3 
        map_keys[52] = Key.K4 ; map_keys[53] = Key.K5 ; map_keys[54] = Key.K6 ; map_keys[55] = Key.K7
        map_keys[56] = Key.K8 ; map_keys[57] = Key.K9

        def KeyBoardFunc(key: str, x: int, y: int) -> None:
            modifiers = glutGetModifiers()
            if modifiers == 0:
                if 'a' <= key <= 'z': key -= 32
            elif modifiers == GLUT_ACTIVE_SHIFT:
                pge.olc_UpdateKeyState(Key.SHIFT, True)
            elif modifiers == GLUT_ACTIVE_CTRL:
                if 'a' <= key <= 'z': key -= 32
                pge.olc_UpdateKeyState(Key.CTRL, True)
            elif modifiers == GLUT_ACTIVE_ALT:
                if 'a' <= key <= 'z': key -= 32
            if map_keys[key]:
                pge.olc_UpdateKeyState(map_keys[key], True)
        glutKeyboardFunc(KeyBoardFunc)

        def KeyBoardUpFunc(key: str, x: int, y: int) -> None:
            modifiers = glutGetModifiers()
            if modifiers == 0:
                if 'a' <= key <= 'z': key -= 32
            elif modifiers == GLUT_ACTIVE_SHIFT:
                pge.olc_UpdateKeyState(Key.SHIFT, False)
            elif modifiers == GLUT_ACTIVE_CTRL:
                if 'a' <= key <= 'z': key -= 32
                pge.olc_UpdateKeyState(Key.CTRL, False)
            elif modifiers == GLUT_ACTIVE_ALT:
                if 'a' <= key <= 'z': key -= 32
            if map_keys[key]:
                pge.olc_UpdateKeyState(map_keys[key], False)
        glutKeyboardUpFunc(KeyBoardUpFunc)

        def SpecialFunc(key: int, x: int, y: int) -> None:
            if map_keys[key]:
                pge.olc_UpdateKeyState(map_keys[key], True)
        glutSpecialFunc(SpecialFunc)

        def SpecialUpFunc(key: int, x: int, y: int) -> None:
            if map_keys[key]:
                pge.olc_UpdateKeyState(map_keys[key], False)
        glutSpecialUpFunc(SpecialUpFunc)

        def MouseFunc(button: int, state: int, x: int, y: int) -> None:
            if button == GLUT_LEFT_BUTTON:
                if state == GLUT_UP: pge.olc_UpdateMouseState(0, False)
                elif state == GLUT_DOWN: pge.olc_UpdateMouseState(0, True)
            elif button == GLUT_MIDDLE_BUTTON:
                if state == GLUT_UP: pge.olc_UpdateMouseState(2, False)
                elif state == GLUT_DOWN: pge.olc_UpdateMouseState(2, True)
            elif button == GLUT_RIGHT_BUTTON:
                if state == GLUT_UP: pge.olc_UpdateMouseState(1, False)
                elif state == GLUT_DOWN: pge.olc_UpdateMouseState(1, True)
        glutMouseFunc(MouseFunc)

        def MouseMoveCall(x: int, y: int) -> None:
            pge.olc_UpdateMouse(x, y);
        glutMotionFunc(MouseMoveCall)
        glutPassiveMotionFunc(MouseMoveCall)

        def EntryFunc(state: int) -> None:
            if state == GLUT_ENTERED: pge.olc_UpdateKeyFocus(True)
            elif state == GLUT_LEFT: pge.olc_UpdateKeyFocus(False)
        glutEntryFunc(EntryFunc)

        def DrawFunc() -> None:
            pge.olc_CoreUpdate()

        def ThreadFunc() -> None:
            if not self.active_ref:
                self.ExitMainLoop()
                self.ThreadCleanUp()
                self.ApplicationCleanUp()
                sys.exit(0)
            glutPostRedisplay()
        glutDisplayFunc(DrawFunc)
        glutIdleFunc(ThreadFunc)
        return ReturnCode.OK

    def SetWindowTitle(self, title: str) -> None:
        glutSetWindowTitle(title)
        return ReturnCode.OK

    def StartSystemEventLoop(self) -> None:
        glutMainLoop()
        return ReturnCode.OK

    def HandleSystemEvent(self) -> None:
        return ReturnCode.OK

class PGEX:

    def __init__(self, hook: bool=False):
        self.hook = hook
        
    def OnBeforeUserCreate(self) -> None: pass
    def OnAfterUserCreate(self) -> None: pass
    def OnBeforeUserUpdate(self, elapsed_time: float) -> None: return False
    def OnAfterUserUpdate(self, elapsed_time: float) -> None: pass

class PixelGameEngine:

    def __init__(self):
        self.app_name: str = "Undefined"
        self.draw_target: Sprite = None
        self.pixel_mode: PixelMode = PixelMode.NORMAL
        self.blend_factor: float = 1.0
        self.screen_size: vi2d = vi2d(256, 240)
        self.inv_screen_size: vf2d = vf2d(1.0 / 256.0, 1.0 / 240.0)
        self.pixel_size: vi2d = vi2d(4, 4)
        self.screen_pixel_size: vi2d = vi2d(4, 4)
        self.mouse_pos: vi2d = vi2d(0, 0)
        self.mouse_wheel_delta: int = 0
        self.mouse_pos_cache: vi2d = vi2d(0, 0)
        self.mouse_window_pos: vi2d = vi2d(0, 0)
        self.mouse_wheel_delta_cache: int = 0
        self.window_size: vi2d = vi2d(0, 0)
        self.view_pos: vi2d = vi2d(0, 0)
        self.view_size: vi2d = vi2d(0, 0)
        self.fullscreen: bool = False
        self.pixel: vf2d = vf2d(1.0, 1.0)
        self.has_input_focus: bool = False
        self.has_mouse_focus: bool = False
        self.enable_vsync: bool = False
        self.frame_timer: float = 1.0
        self.last_elapsed: float = 0.0
        self.frame_count: int = 0
        self.font_sprite: Sprite = None
        self.font_decal: Decal = None # 1129
        self.layers: List[LayerDesc] = []
        self.target_layer: int = 0
        self.last_fps: int = 0
        self.pixel_cohesion: bool = False
        self.decal_mode: Decal.DecalMode = Decal.DecalMode.NORMAL
        self.decal_structure: Decal.DecalStructure = Decal.DecalStructure.FAN
        self.func_pixel_mode: Callable = None #(self, int, int, pixel, pixel)
        self.font_spacing: List[vi2d] = []

        self.key_new_state: List[bool] = [False] * 256
        self.key_old_state: List[bool] = [False] * 256
        self.keyboard_state: List[HWButton] = [None] * 256

        self.mouse_new_state: List[bool] = [False] * MOUSE_BUTTONS
        self.mouse_old_state: List[bool] = [False] * MOUSE_BUTTONS
        self.mouse_state: List[HWButton] = [False] * MOUSE_BUTTONS

        self.atom_active = None

        self.tp1: float = 0.0
        self.tp2: float = 0.0

        self.extensions: List[PGEX] = []
    
    def Construct(self, screen_w: int, screen_h: int, pixel_w: int, pixel_h: int, full_screen: bool=False, vsync: bool=False, cohesion: bool=False) -> ReturnCode:
        self.pixel_cohesion = cohesion
        self.screen_size = vi2d(screen_w, screen_h)
        self.inv_screen_size = vf2d(1.0 / screen_w, 1.0 / screen_h)
        self.pixel_size = vi2d(pixel_w, pixel_h)
        self.window_size = self.screen_size * self.pixel_size
        self.fullscreen = full_screen
        self.enable_vsync = vsync
        self.pixel = vf2d(2.0 / self.screen_size.x, 2.0 / self.screen_size.y)

        if self.pixel_size.x <= 0 or self.pixel_size.y <= 0 or self.screen_size.x <= 0 or self.screen_size.y <= 0:
            return ReturnCode.FAIL
        return ReturnCode.OK

    def SetScreenSize(self, w: int, h: int) -> None:
        self.screen_size = vi2d(w, h)
        self.inv_screen_size = vf2d(1.0 / w, 1.0 / h)
        for layer in self.layers:
            layer.target.Create(self.screen_size.x, self.screen_size.y)
            layer.update = True
        self.SetDrawTarget(None)
        renderer.ClearBuffer(BLACK, True)
        renderer.DisplayFrame()
        renderer.ClearBuffer(BLACK, True)
        renderer.UpdateViewport(self.view_pos, self.view_size)

    def Start(self) -> None:
        if platform_instance.ApplicationStartUp() != ReturnCode.OK:
            return ReturnCode.FAIL
        if platform_instance.CreateWindowPane(vi2d(30, 30), self.window_size, self.fullscreen) != ReturnCode.OK:
            return ReturnCode.FAIL
        self.olc_UpdateWindowSize(self.window_size.x, self.window_size.y)
        self.atom_active = True
        thread = Thread(target=self.EngineThread)
        thread.start()
        #self.EngineThread()
        platform_instance.StartSystemEventLoop()
        thread.join()
        if not platform_instance.ApplicationCleanUp():
            return ReturnCode.FAIL
        return ReturnCode.OK


    # Override Interfaces

    def OnUserCreate(self) -> None: pass
    def OnUserUpdate(self, elapsed_time: float) -> None: pass
    def OnUserDestroy(self) -> None: pass

    # Hardware Interfaces

    def IsFocused(self) -> bool:
        return self.has_input_focus

    def GetKey(self, key: Key) -> HWButton:
        return self.keyboard_state[key]

    def GetMouse(self, b: int) -> HWButton:
        return self.mouse_state[b]

    def GetMouseX(self) -> int:
        return self.mouse_pos.x

    def GetMouseY(self) -> int:
        return self.mouse_pos.y

    def GetMouseWheel(self) -> int:
        return self.mouse_wheel_delta

    def GetWindowMouse(self) -> v2d_generic:
        return self.mouse_pos

    def GetMousePos(self) -> v2d_generic:
        return self.mouse_window_pos

    @staticmethod
    def GetKeyMap(self) -> Dict[Key, HWButton]: return map_keys

    # Utility

    def ScreenWidth(self) -> int:
        return self.screen_size.x

    def ScreenHeight(self) -> int:
        return self.screen_size.y

    def GetDrawTargetWidth(self) -> int:
        if self.draw_target:
            return self.draw_target.w
        return 0

    def GetDrawTargetHeight(self) -> int:
        if self.draw_target:
            return self.draw_target.h
        return 0

    def GetDrawTarget(self) -> Sprite:
        return self.draw_target

    def GetFPS(self) -> int:
        return self.last_fps

    def GetElapsedTime(self) -> float:
        return self.last_elapsed

    def GetWindowSize(self) -> v2d_generic:
        return self.window_size

    def GetPixelSize(self) -> v2d_generic:
        return self.pixel_size

    def GetScreenPixelSize(self) -> v2d_generic:
        return self.screen_pixel_size

    # Configuration Routines

    def SetDrawTarget(self, target: Union[Sprite, int]) -> None:
        if isinstance(target, Sprite):
            if target:
                self.draw_target = target
            else:
                self.target_layer = 0
                self.draw_target = self.layers[0].target.Sprite()
        elif isinstance(target, int):
            if target < len(self.layers):
                self.draw_target = self.layers[target].target.Sprite()
                self.layers[target].update = True
                self.target_layer = target

    def EnableLayer(self, layer: int, enable: bool) -> None:
        if layer < len(self.layers):
            self.layers[layer].show = enable

    def SetLayerOffset(self, layer: int, x: float, y: float) -> None:
        if layer < len(self.layers):
            self.layers[layer].offset = vf2d(x, y)

    def SetLayerScale(self, layer: int, x: float, y: float) -> None:
        if layer < len(self.layers):
            self.layers[layer].scale = vf2d(x, y)

    def SetLayerTint(self, layer: int, tint: Pixel) -> None:
        if layer < len(self.layers):
            self.layers[layer].tint = tint

    def SetLayerCustomRenderFunction(self, layer: int, func: Callable[[], None]) -> None:
        if layer < len(self.layers):
            self.layers[layer].custom_render = func

    def GetLayers(self) -> List[int]:
        return self.layers

    def GetVisibleLayers(self) -> List[int]:
        return [layer for layer in self.layers if layer.show]

    def CreateLayer(self) -> int:
        layer = LayerDesc()
        layer.target.Create(self.screen_size.x, self.screen_size.y)
        self.layers.append(layer)
        return int(len(self.layers)) - 1

    def SetPixelMode(self, mode: PixelMode) -> None:
        self.pixel_mode = mode

    def GetPixelMode(self) -> PixelMode:
        return self.pixel_mode

    def SetPixelBlend(self, blend: float) -> None:
        self.pixel_blend = blend

    # Drawing Routines

    @singledispatchmethod
    def Draw(self, arg) -> bool:
        raise NotImplementedError(f"PixelGameEngine.Draw: Invalid Arugment: {arg}")

    @Draw.register
    def _(self, x: int, y: int, p: Pixel=WHITE) -> bool:
        if not self.draw_target:
            return False
        if self.pixel_mode == PixelMode.NORMAL:
            return self.draw_target.SetPixel(x, y, p)
        if self.pixel_mode == PixelMode.MASK:
            if p.a == 255:
                return self.draw_target.SetPixel(x, y, p)
        if self.pixel_mode == PixelMode.ALPHA:
            d = self.draw_target.GetPixel(x, y)
            a = float(p.a / 255.0) * self.blend_factor
            c = 1.0 - a
            r = a * float(p.r) + c * float(d.r)
            g = a * float(p.g) + c * float(d.g)
            b = a * float(p.b) + c * float(d.b)
            return self.draw_target.SetPixel(x, y, Pixel(int(r), int(g), int(b), 255))

    @Draw.register
    def _(self, pos: v2d_generic, p: Pixel=WHITE) -> bool:
        return self.Draw(pos.x, pos.y, p)

    @singledispatchmethod
    def DrawLine(self, arg) -> None:
        raise NotImplementedError(f"PixelGameEngine.DrawLine: Invalid Arugment: {arg}")
    
    @DrawLine.register
    def _(self, x1: int, y1: int, x2: int, y2: int, p: Pixel=WHITE, pattern: int=0xFFFFFFFF) -> None:
        dx = x2 - x1
        dy = y2 - y1

        def rol() -> int:
            return ((pattern << 1) | (pattern >> 31)) & 1
        
        p1 = vi2d(x1, y1)
        p2 = vi2d(x2, y2)
        x1 = p1.x
        y1 = p1.y
        x2 = p2.x
        y2 = p2.y

        if dx == 0:
            if y2 < y1: y1, y2 = y2, y1
            for y in range(y1, y2 + 1):
                if rol():
                    self.Draw(x1, y, p)
            return
        
        if dy == 0:
            if x2 < x1: x1, x2 = x2, x1
            for x in range(x1, x2 + 1):
                if rol():
                    self.Draw(x, y1, p)
            return

        dx1 = abs(dx)
        dy1 = abs(dy)
        px = 2 * dy1 - dx1
        py = 2 * dx1 - dy1

        if dy1 <= dx1:
            x = x1 if dx >= 0 else x2
            y = y1 if dx >= 0 else y2
            xe = x2 if dx >= 0 else x1
            if rol():
                self.Draw(x, y, p)
            while x < xe:
                x += 1
                if px < 0:
                    px += 2 * dy1
                else:
                    if (dx < 0 and dy < 0) or (dx > 0 and dy > 0):
                        y += 1
                    else:
                        y -= 1
                    px += 2 * (dy1 - dx1)
                if rol():
                    self.Draw(x, y, p)
        else:
            y = y1 if dy >= 0 else y2
            x = x1 if dy >= 0 else x2
            ye = y2 if dy >= 0 else y1
            if rol():
                self.Draw(x, y, p)
            while y < ye:
                y += 1
                if py < 0:
                    py += 2 * dx1
                else:
                    if (dx < 0 and dy < 0) or (dx > 0 and dy > 0):
                        x += 1
                    else:
                        x -= 1
                    py += 2 * (dx1 - dy1)
                if rol():
                    self.Draw(x, y, p)

    @DrawLine.register
    def _(self, pos1: v2d_generic, pos2: v2d_generic, p: Pixel=WHITE, pattern: int=0xFFFFFFFF) -> None:
        self.DrawLine(pos1.x, pos1.y, pos2.x, pos2.y, p, pattern)

    @singledispatchmethod
    def DrawCircle(self, arg) -> None:
        raise NotImplementedError(f"PixelGameEngine.DrawCircle: Invalid Arugment: {arg}")

    @DrawCircle.register
    def _(self, x: int, y: int, radius: int, p: Pixel=WHITE, mask: int=0xFF) -> None:
        if radius < 0 or x < -radius or x - self.GetDrawTargetWidth() > radius or y - self.GetDrawTargetHeight() > radius:
            return
        if radius > 0:
            x0 = 0
            y0 = radius
            d = 3 - 2 * radius

            while y0 >= x0:
                if mask & 0x01: self.Draw(x + x0, y - y0, p)
                if mask & 0x04: self.Draw(x + y0, y + x0, p)
                if mask & 0x10: self.Draw(x - x0, y + y0, p)
                if mask & 0x40: self.Draw(x - y0, y - x0, p)
                if x0 != 0 and x0 != y0:
                    if mask & 0x02: self.Draw(x + y0, y - x0, p)
                    if mask & 0x08: self.Draw(x + x0, y + y0, p)
                    if mask & 0x20: self.Draw(x - y0, y + x0, p)
                    if mask & 0x80: self.Draw(x - x0, y - y0, p)
                if d < 0:
                    x0 += 1
                    d += 4 * x0 + 6
                else:
                    x0 += 1
                    y0 -= 1
                    d += 4 * (x0 - y0) + 10
        else:
            self.Draw(x, y, p)

    @DrawCircle.register
    def _(self, pos: v2d_generic, radius: int, p: Pixel=WHITE, mask: int=0xFF) -> None:
        self.DrawCircle(pos.x, pos.y, radius, p, mask)

    @singledispatchmethod
    def FillCircle(self, arg) -> None:
        raise NotImplementedError(f"PixelGameEngine.FillCircle: Invalid Arugment: {arg}")

    @FillCircle.register
    def _(self, x: int, y: int, radius: int, p: Pixel=WHITE) -> None:
        if radius < 0 or x < -radius or x - self.GetDrawTargetWidth() > radius or y - self.GetDrawTargetHeight() > radius:
            return
        if radius > 0:
            x0 = 0
            y0 = radius
            d = 3 - 2 * radius

            def DrawLineShortcut(sx: int, ex: int, y: int) -> None:
                for x in range(sx, ex + 1):
                    self.Draw(x, y, p)
            
            while y0 >= x0:
                DrawLineShortcut(x - y0, x + y0, y - x0)
                if x0 > 0:
                    DrawLineShortcut(x - y0, x + y0, y + x0)
                if d < 0:
                    x0 += 1
                    d += 4 * x0 + 6
                else:
                    if x0 != y0:
                        DrawLineShortcut(x - x0, x + x0, y - y0)
                        DrawLineShortcut(x - x0, x + x0, y + y0)
                    x0 += 1
                    y0 -= 1
                    d += 4 * (x0 - y0) + 10
        else:
            self.Draw(x, y, p)

    @FillCircle.register
    def _(self, pos: v2d_generic, radius: int, p: Pixel=WHITE) -> None:
        self.FillCircle(pos.x, pos.y, radius, p)

    @singledispatchmethod
    def DrawRect(self, arg) -> None:
        raise NotImplementedError(f"PixelGameEngine.DrawRect: Invalid Arugment: {arg}")

    @DrawRect.register
    def _(self, x: int, y: int, w: int, h: int, p: Pixel=WHITE) -> None:
        self.DrawLine(x, y, x + w, y, p)
        self.DrawLine(x + w, y, x + w, y + h, p)
        self.DrawLine(x + w, y + h, x, y + h, p)
        self.DrawLine(x, y + h, x, y, p)

    @DrawRect.register
    def _(self, pos: v2d_generic, size: v2d_generic, p: Pixel=WHITE) -> None:
        self.DrawRect(pos.x, pos.y, size.x, size.y, p)

    @singledispatchmethod # 2144 
    def FillRect(self, arg) -> None:
        raise NotImplementedError(f"PixelGameEngine.FillRect: Invalid Arugment: {arg}")
    @FillRect.register
    def _(self, x: int, y: int, w: int, h: int, p: Pixel=WHITE) -> None: pass
    @FillRect.register
    def _(self, pos: v2d_generic, size: v2d_generic, p: Pixel=WHITE) -> None: pass

    @singledispatchmethod
    def DrawTriangle(self, arg) -> None:
        raise NotImplementedError(f"PixelGameEngine.DrawTriangle: Invalid Arugment: {arg}")
    @DrawTriangle.register
    def _(self, x1: int, y1: int, x2: int, y2: int, x3: int, y3: int, p: Pixel=WHITE) -> None: pass
    @DrawTriangle.register
    def _(self, pos1: v2d_generic, pos2: v2d_generic, pos3: v2d_generic, p: Pixel=WHITE) -> None: pass

    @singledispatchmethod
    def FillTriangle(self, arg) -> None:
        raise NotImplementedError(f"PixelGameEngine.FillTriangle: Invalid Arugment: {arg}")
    @FillTriangle.register
    def _(self, x1: int, y1: int, x2: int, y2: int, x3: int, y3: int, p: Pixel=WHITE) -> None: pass
    @FillTriangle.register
    def _(self, pos1: v2d_generic, pos2: v2d_generic, pos3: v2d_generic, p: Pixel=WHITE) -> None: pass

    @singledispatchmethod
    def DrawSprite(self, arg) -> None:
        raise NotImplementedError(f"PixelGameEngine.DrawSprite: Invalid Arugment: {arg}")
    @DrawSprite.register
    def _(self, x: int, y: int, sprite: Sprite, scale: int=1, flip: int=Sprite.SpriteFlip.NONE) -> None: pass
    @DrawSprite.register
    def _(self, pos: v2d_generic, sprite: Sprite, scale: int=1, flip: int=Sprite.SpriteFlip.NONE) -> None: pass

    @singledispatchmethod
    def DrawPartialSprite(self, arg) -> None:
        raise NotImplementedError(f"PixelGameEngine.DrawPartialSprite: Invalid Arugment: {arg}")
    @DrawPartialSprite.register
    def _(self, x: int, y: int, sprite: Sprite, ox: int, oy: int, w: int, h: int, scale: int=1, flip: int=Sprite.SpriteFlip.NONE) -> None: pass
    @DrawPartialSprite.register
    def _(self, pos: v2d_generic, sprite: Sprite, ox: int, oy: int, w: int, h: int, scale: int=1, flip: int=Sprite.SpriteFlip.NONE) -> None: pass

    @singledispatchmethod
    def DrawString(self, arg) -> None:
        raise NotImplementedError(f"PixelGameEngine.DrawString: Invalid Arugment: {arg}")
    @DrawString.register
    def _(self, x: int, y: int, text: str, color: Pixel=WHITE, scale: int=1) -> None: pass
    @DrawString.register
    def _(self, pos: v2d_generic, text: str, color: Pixel=WHITE, scale: int=1) -> None: pass
    def GetTextSize(self, text: str) -> v2d_generic: pass

    @singledispatchmethod
    def DrawStringProp(self, arg) -> None:
        raise NotImplementedError(f"PixelGameEngine.DrawStringProp: Invalid Arugment: {arg}")
    @DrawStringProp.register
    def _(self, x: int, y: int, text: str, color: Pixel=WHITE, scale: int=1) -> None: pass
    @DrawStringProp.register
    def _(self, pos: v2d_generic, text: str, color: Pixel=WHITE, scale: int=1) -> None: pass
    def GetTextSizeProp(self, text: str) -> v2d_generic: pass

    def SetDecalMode(self, mode: Decal.DecalMode) -> None: pass
    def SetDecalStructure(self, structure: Decal.DecalStructure) -> None: pass
    
    def DrawDecal(self, pos: v2d_generic, decal: Decal, scale: List[float]=[1.0, 1.0], tint: Pixel=WHITE) -> None: pass

    @singledispatchmethod
    def DrawPartialDecal(self, arg) -> None:
        raise NotImplementedError(f"PixelGameEngine.DrawPartialDecal: Invalid Arugment: {arg}")
    @DrawPartialDecal.register
    def _(self, pos: v2d_generic, decal: Decal, source_pos: v2d_generic, source_size: v2d_generic, scale: List[float]=[1.0, 1.0], tint: Pixel=WHITE) -> None: pass
    @DrawPartialDecal.register
    def _(self, pos: v2d_generic, size: v2d_generic, decal: Decal, source_pos: v2d_generic, source_size: v2d_generic, tint: Pixel=WHITE) -> None: pass

    def DrawExplicitDecal(self, decal: Decal, pos: v2d_generic, uv: v2d_generic, color: Pixel, elements:int=4) -> None: pass
    def DrawWarpedDecal(self, decal: Decal, pos: v2d_generic, tint: Pixel=WHITE) -> None: pass
    def DrawPartialWarpedDecal(self, decal: Decal, pos: v2d_generic, source_pos: v2d_generic, source_size: v2d_generic, tint: Pixel=WHITE) -> None: pass
    def DrawRotatedDecal(self, pos: v2d_generic, decal: Decal, angle: float, tint: Pixel=WHITE) -> None: pass
    def DrawPartialRotatedDecal(self, pos: v2d_generic, decal: Decal, angle: float, center: v2d_generic, source_pos: v2d_generic, source_size: v2d_generic, scale: List[float]=[1.0, 1.0], tint: Pixel=WHITE) -> None: pass
    def DrawStringDecal(self, pos: v2d_generic, text: str, color: Pixel=WHITE, scale: List[float]=[1.0, 1.0]) -> None: pass
    def DrawStringPropDecal(self, pos: v2d_generic, text: str, color: Pixel=WHITE, scale: List[float]=[1.0, 1.0]) -> None: pass
    def FillRectDecal(self, pos: v2d_generic, size: v2d_generic, color: Pixel=WHITE) -> None: pass
    def GradientFillRectDecal(self, pos: v2d_generic, size: v2d_generic, colorTL: Pixel, colorBL: Pixel, colorBR: Pixel, colorTR: Pixel) -> None: pass

    @singledispatchmethod
    def DrawPolygonDecal(self, arg) -> None:
        raise NotImplementedError(f"PixelGameEngine.DrawPolygonDecal: Invalid Arugment: {arg}")
    @DrawPolygonDecal.register
    def _(self, decal: Decal, pos: List[v2d_generic], uv: List[v2d_generic], tint: Pixel=WHITE) -> None: pass
    @DrawPolygonDecal.register
    def _(self, decal: Decal, pos: List[v2d_generic], depth: List[float], uv: List[v2d_generic], tint: Pixel=WHITE) -> None: pass
    @DrawPolygonDecal.register
    def _(self, decal: Decal, pos: List[v2d_generic], uv: List[v2d_generic], tint: List[Pixel]) -> None: pass

    def DrawLineDecal(self, pos1: v2d_generic, pos2: v2d_generic, p: Pixel=WHITE) -> None: pass
    def DrawRotatedStringDecal(self, pos: v2d_generic, text: str, angle: float, center: List[float]=[0.0, 0.0], color: Pixel=WHITE, scale: List[float]=[1.0, 1.0]) -> None: pass
    def DrawRotatedStringPropDecal(self, pos: v2d_generic, text: str, angle: float, center: List[float]=[0.0, 0.0], color: Pixel=WHITE, scale: List[float]=[1.0, 1.0]) -> None: pass

    def Clear(self, color: Pixel) -> None:
        pixels = self.GetDrawTargetWidth() * self.GetDrawTargetHeight()
        m = self.GetDrawTarget().GetData()
        for idx, _ in enumerate(pixels):
            m[idx] = color

    def ClearBuffer(self, color: Pixel, depth: bool=True) -> None:
        renderer.ClearBuffer(color, depth)

    def GetFontSprite(self) -> Sprite:
        return self.font_sprite

    def ClipLineToScreen(self, in_p1: v2d_generic, in_p2: v2d_generic) -> bool:
        SEG_I = 0b0000
        SEG_L = 0b0001
        SEG_R = 0b0010
        SEG_B = 0b0100
        SEG_T = 0b1000

        def Segment(v: v2d_generic) -> int:
            i = SEG_I
            if v.x < 0:
                i |= SEG_L
            elif v.x > self.screen_size.x:
                i |= SEG_R
            if v.y < 0:
                i |= SEG_B
            elif v.y > self.screen_size.y:
                i |= SEG_T
            return i

        s1 = Segment(in_p1)
        s2 = Segment(in_p2)

        while True:
            if not (s1 | s2): return True
            if s1 & s2: return False
            s3 = s2 if s2 > s2 else s1
            n = vi2d(0, 0)
            if s3 & SEG_T:
                n.x = in_p1.x + (in_p2.x - in_p1.x) * (self.screen_size.y - in_p1.y) / (in_p2.y - in_p1.y)
                n.y = self.screen_size.y
            elif s3 & SEG_B:
                n.x = in_p1.x + (in_p2.x - in_p1.x) * (0 - in_p1.y) / (in_p2.y - in_p1.y)
                n.y = 0
            elif s3 & SEG_R:
                n.x = self.screen_size.x
                n.y = in_p1.y + (in_p2.y - in_p1.y) * (self.screen_size.x - in_p1.x) / (in_p2.x - in_p1.x)
            elif s3 & SEG_L:
                n.x = 0
                n.y = in_p1.y + (in_p2.y - in_p1.y) * (0 - in_p1.x) / (in_p2.x - in_p1.x)
            if s3 == s1:
                in_p1 = n
                s1 = Segment(in_p1)
            else:
                in_p2 = n
                s2 = Segment(in_p2) 

    def EngineThread(self) -> None:
        if platform_instance.ThreadStartUp() == ReturnCode.FAIL:
            return
        
        self.olc_PrepareEngine()

        for ext in self.extensions:
            ext.OnBeforeUserCreate()
        if not self.OnUserCreate():
            self.atom_active = False
        for ext in self.extensions:
            ext.OnAfterUserCreate()
        
        while self.atom_active:
            while self.atom_active:
                self.olc_CoreUpdate()
            if not self.OnUserDestroy():
                self.atom_active = True
        platform_instance.ThreadCleanUp()
        

    # "Break In" Functions

    def olc_UpdateMouse(self, x: int, y: int) -> None:
        self.has_mouse_focus = True
        self.mouse_window_pos = vi2d(x, y)
        x -= self.view_pos.x
        y -= self.view_pos.y
        self.mouse_pos_cache.x = int(((float(x) / float(self.window_size.x - (self.view_pos.x * x)) * float(self.screen_size.x))))
        self.mouse_pos_cache.y = int(((float(y) / float(self.window_size.y - (self.view_pos.y * y)) * float(self.screen_size.y))))
        if self.mouse_pos_cache.x >= int(self.screen_size.x):
            self.mouse_pos_cache.x = self.screen_size.x - 1
        if self.mouse_pos_cache.y >= int(self.screen_size.y):
            self.mouse_pos_cache.y = self.screen_size.y - 1
        if self.mouse_pos_cache.x < 0:
            self.mouse_pos_cache.x = 0
        if self.mouse_pos_cache.y < 0:
            self.mouse_pos_cache.y = 0

    def olc_UpdateMouseWheel(self, delta: int) -> None:
        self.mouse_wheel_delta_cache += delta

    def olc_UpdateWindowSize(self, x: int, y: int) -> None:
        self.window_size = vi2d(x, y)
        self.olc_UpdateViewport()

    def olc_UpdateViewport(self) -> None:
        ww = self.window_size.x * self.pixel_size.x
        wh = self.window_size.y * self.pixel_size.y
        wasp = float(ww) / float(wh)

        if self.pixel_cohesion:
            self.screen_pixel_size = self.window_size / self.screen_size
            self.view_size = (self.window_size / self.screen_size) * self.screen_size
        else:
            self.view_size.x = int(self.window_size.x)
            self.view_size.y = int(float(self.window_size.y) / wasp)

            if self.view_size.y > self.window_size.y:
                self.view_size.y = self.window_size.y
                self.view_size.x = int(float(self.view_size.y) * wasp)
        self.view_pos = vi2d(int((self.window_size.x - self.view_size.x) / 2), int((self.window_size.y - self.view_size.y) / 2))

    def olc_ConstructFontSheet(self) -> None:
        data = ""
        data += "?Q`0001oOch0o01o@F40o0<AGD4090LAGD<090@A7ch0?00O7Q`0600>00000000"
        data += "O000000nOT0063Qo4d8>?7a14Gno94AA4gno94AaOT0>o3`oO400o7QN00000400"
        data += "Of80001oOg<7O7moBGT7O7lABET024@aBEd714AiOdl717a_=TH013Q>00000000"
        data += "720D000V?V5oB3Q_HdUoE7a9@DdDE4A9@DmoE4A;Hg]oM4Aj8S4D84@`00000000"
        data += "OaPT1000Oa`^13P1@AI[?g`1@A=[OdAoHgljA4Ao?WlBA7l1710007l100000000"
        data += "ObM6000oOfMV?3QoBDD`O7a0BDDH@5A0BDD<@5A0BGeVO5ao@CQR?5Po00000000"
        data += "Oc``000?Ogij70PO2D]??0Ph2DUM@7i`2DTg@7lh2GUj?0TO0C1870T?00000000"
        data += "70<4001o?P<7?1QoHg43O;`h@GT0@:@LB@d0>:@hN@L0@?aoN@<0O7ao0000?000"
        data += "OcH0001SOglLA7mg24TnK7ln24US>0PL24U140PnOgl0>7QgOcH0K71S0000A000"
        data += "00H00000@Dm1S007@DUSg00?OdTnH7YhOfTL<7Yh@Cl0700?@Ah0300700000000"
        data += "<008001QL00ZA41a@6HnI<1i@FHLM81M@@0LG81?O`0nC?Y7?`0ZA7Y300080000"
        data += "O`082000Oh0827mo6>Hn?Wmo?6HnMb11MP08@C11H`08@FP0@@0004@000000000"
        data += "00P00001Oab00003OcKP0006@6=PMgl<@440MglH@000000`@000001P00000000"
        data += "Ob@8@@00Ob@8@Ga13R@8Mga172@8?PAo3R@827QoOb@820@0O`0007`0000007P0"
        data += "O`000P08Od400g`<3V=P0G`673IP0`@3>1`00P@6O`P00g`<O`000GP800000000"
        data += "?P9PL020O`<`N3R0@E4HC7b0@ET<ATB0@@l6C4B0O`H3N7b0?P01L3R000000020"

        self.font_sprite = Sprite(w=128, h=48)
        px = 0
        py = 0
        for b in range(0, 1024, 4):
            sym1 = ord(data[b + 0]) - 48
            sym2 = ord(data[b + 1]) - 48
            sym3 = ord(data[b + 2]) - 48
            sym4 = ord(data[b + 3]) - 48
            r = sym1 << 18 | sym2 << 12 | sym3 << 6 | sym4
            for i in range(0, 24):
                k = 255 if r & (1 << i) else 0
                self.font_sprite.SetPixel(px, py, Pixel(k, k, k, k))
                py += 1
                if py == 48:
                    px += 1
                    py = 0
        
        self.font_decal = Decal(self.font_sprite)

        spacing: List[int] = [
            0x03,0x25,0x16,0x08,0x07,0x08,0x08,0x04,0x15,0x15,0x08,0x07,0x15,0x07,0x24,0x08,
            0x08,0x17,0x08,0x08,0x08,0x08,0x08,0x08,0x08,0x08,0x24,0x15,0x06,0x07,0x16,0x17,
            0x08,0x08,0x08,0x08,0x08,0x08,0x08,0x08,0x08,0x17,0x08,0x08,0x17,0x08,0x08,0x08,
            0x08,0x08,0x08,0x08,0x17,0x08,0x08,0x08,0x08,0x17,0x08,0x15,0x08,0x15,0x08,0x08,
            0x24,0x18,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x33,0x17,0x17,0x33,0x18,0x17,0x17,
            0x17,0x17,0x17,0x17,0x07,0x17,0x17,0x18,0x18,0x17,0x17,0x07,0x33,0x07,0x08,0x00
        ]

        for c in spacing:
            self.font_spacing.append(vi2d(c >> 4, c & 15))


    def olc_CoreUpdate(self) -> None:
        self.tp2 = time.time()
        self.elapsed_time = self.tp2 - self.tp1
        self.tp1 = self.tp2
        
        platform_instance.HandleSystemEvent()

        def ScanHardware(keys: List[HWButton], old_states: List[bool], new_states: List[bool], key_count: int) -> None:
            for i in range(key_count):
                keys[i].pressed = False
                keys[i].released = False
                if new_states[i] != old_states[i]:
                    if new_states[i]:
                        keys[i].pressed = not keys[i].held
                        keys[i].help = True
                    else:
                        keys[i].released = True
                        keys[i].held = False
                old_states[i] = new_states[i]

        ScanHardware(self.keyboard_state, self.key_old_state, self.key_new_state, 256)
        ScanHardware(self.mouse_state, self.mouse_old_state, self.mouse_new_state, MOUSE_BUTTONS)

        self.mouse_pos = self.mouse_pos_cache
        self.mouse_wheel_delta = self.mouse_wheel_delta_cache
        self.mouse_wheel_delta_cache = 0

        extension_block_frame = False
        for ext in self.extensions:
            extension_block_frame |= ext.OnBeforeUserUpdate(self.elapsed_time)
        if not extension_block_frame:
            if not self.OnUserUpdate(self.elapsed_time):
                self.atom_active = False
        for ext in self.extensions:
            ext.OnAfterUserUpdate(self.elapsed_time)
        
        renderer.UpdateViewport(self.view_pos, self.view_size)
        renderer.ClearBuffer(BLACK, True)

        self.layers[0].update = True
        self.layers[0].show = True
        self.SetDecalMode(Decal.DecalMode.DECAL)
        renderer.PrepareDrawing()

        for layer in self.layers:
            if layer.show:
                if layer.func_hook == None:
                    renderer.ApplyTexture(layer.target.Decal().id)
                    if layer.update:
                        layer.target.Decal().Update()
                        layer.update = False
                    renderer.DrawLayerQuad(layer.offset, layer.scale, layer.tint)
                    for decal in layer.decal_instances:
                        renderer.DrawDecal(decal)
                    layer.decal_instances.clear()
                else:
                    layer.func_hook()
        
        renderer.DisplayFrame()

        self.frame_timer += self.elapsed_time
        self.frame_count += 1
        if self.frame_timer >= 1.0:
            self.last_fps = self.frame_count
            self.frame_timer -= 1.0
            title = f"OneLoneCoder.com - Pixel Game Engine - {self.app_name} - FPS: {self.last_fps}"
            platform_instance.SetWindowTitle(title)
            self.frame_count = 0

    def olc_PrepareEngine(self) -> None:
        if platform_instance.CreateGraphics(self.fullscreen, self.enable_vsync, self.view_pos, self.view_size) == ReturnCode.FAIL:
            return
        self.olc_ConstructFontSheet()

        self.CreateLayer()
        self.layers[0].update = True
        self.layers[0].show = True
        self.SetDrawTarget(None)

        self.tp1 = time.time()
        self.tp2 = time.time()

    def olc_UpdateMouseState(self, button: int, state: bool) -> None:
        self.mouse_new_state[button] = state

    def olc_UpdateKeyState(self, key: int, state: bool) -> None:
        self.key_new_state[key] = state

    def olc_UpdateKeyFocus(self, state: bool) -> None:
        self.has_input_focus = state

    def olc_Terminate(self) -> None:
        self.atom_active = False

    def olc_Reanimate(self) -> None:
        self.atom_active = True

    def olc_IsRunning(self) -> bool:
        return self.atom_active

renderer = Renderer()
platform_instance = Platform()
pge = PixelGameEngine()
map_keys = {} # {size_t: uint8_t}