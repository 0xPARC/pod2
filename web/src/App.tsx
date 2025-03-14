import { PodList } from "./components/pods/PodList";
import { Toaster } from "sonner";

export default function App() {
  return (
    <main className="min-h-screen bg-background">
      <PodList />
      <Toaster />
    </main>
  );
}
