import { createFileRoute } from "@tanstack/react-router";
import { LoginForm } from "../components/LoginForm";
import { UserProfile } from "../components/UserProfile";
import { useUser } from "../contexts/UserContext";

export const Route = createFileRoute("/zoo-deel")({
  component: RouteComponent,
});

function SignPodComponent({ publicKey }: { publicKey: string }) {
  return (
    <div>
      <h1>Sign Pod</h1>
      <p>Public Key: {publicKey}</p>
    </div>
  );
}

function RouteComponent() {
  const { publicKey, isLoggedIn, login, logout } = useUser();

  return isLoggedIn ? (
    <SignPodComponent publicKey={publicKey} />
  ) : (
    <LoginForm onLogin={login} title="Login to Zoo Deel" />
  );
}
