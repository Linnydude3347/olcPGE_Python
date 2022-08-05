from olcPGE import *

class Example(PixelGameEngine):

    def __init__(self):
        super().__init__()
        self.app_name = "Example"
    
    def OnUserCreate(self) -> bool:
        return True
    
    def OnUserUpdate(self, elapsed_time: float) -> bool:
        for x in range(self.ScreenWidth()):
            for y in range(self.ScreenHeight()):
                self.Draw(x, y, WHITE)
        return True

def main():
    ex = Example()
    if ex.Construct(256, 240, 4, 4):
        ex.Start()
    return 0

if __name__ == '__main__':
    main()