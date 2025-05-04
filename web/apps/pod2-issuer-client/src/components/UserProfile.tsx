import { useUser } from "../contexts/UserContext";

interface UserProfileProps {
  username: string;
  onLogout: () => void;
}

export function UserProfile({ username, onLogout }: UserProfileProps) {
  const { publicKey } = useUser();

  return (
    <div className="max-w-md mx-auto mt-10 p-6 bg-white rounded-lg shadow-md">
      <h1 className="text-2xl font-bold mb-4">Welcome, {username}!</h1>
      <p className="mb-2">You are now logged in to the application.</p>
      <p className="mb-4 text-sm text-gray-600">Public Key: {publicKey}</p>
      <button
        onClick={onLogout}
        className="bg-red-500 hover:bg-red-600 text-white font-medium py-2 px-4 rounded"
      >
        Logout
      </button>
    </div>
  );
}
